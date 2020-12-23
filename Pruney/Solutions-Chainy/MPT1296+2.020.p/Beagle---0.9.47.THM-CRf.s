%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 181 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  113 ( 364 expanded)
%              Number of equality atoms :   37 ( 129 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_tarski > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_32,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_1'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_93,plain,(
    ! [A_42,C_43,B_44] :
      ( m1_subset_1(A_42,C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_96,plain,(
    ! [A_42] :
      ( m1_subset_1(A_42,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_42,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_34,B_35] : ~ r2_hidden(A_34,k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k7_setfam_1(A_9,B_10),k1_zfmisc_1(k1_zfmisc_1(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [A_62,B_63] :
      ( k7_setfam_1(A_62,k7_setfam_1(A_62,B_63)) = B_63
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_150,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_155,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k7_setfam_1(A_64,B_65),k1_zfmisc_1(k1_zfmisc_1(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( m1_subset_1(A_17,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_191,plain,(
    ! [A_71,A_72,B_73] :
      ( m1_subset_1(A_71,k1_zfmisc_1(A_72))
      | ~ r2_hidden(A_71,k7_setfam_1(A_72,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(resolution,[status(thm)],[c_155,c_22])).

tff(c_275,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_83,B_84)),k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83)))
      | k7_setfam_1(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_191])).

tff(c_294,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_275])).

tff(c_301,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_294])).

tff(c_302,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_301])).

tff(c_332,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_335,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_332])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_335])).

tff(c_341,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_892,plain,(
    ! [A_110] :
      ( m1_subset_1(A_110,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_110,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_341,c_22])).

tff(c_904,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_892])).

tff(c_905,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_904])).

tff(c_18,plain,(
    ! [A_13,C_16,B_14] :
      ( r2_hidden(k3_subset_1(A_13,C_16),k7_setfam_1(A_13,B_14))
      | ~ r2_hidden(C_16,B_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_943,plain,(
    ! [C_16] :
      ( r2_hidden(k3_subset_1('#skF_2',C_16),k1_xboole_0)
      | ~ r2_hidden(C_16,'#skF_3')
      | ~ m1_subset_1(C_16,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_18])).

tff(c_960,plain,(
    ! [C_16] :
      ( r2_hidden(k3_subset_1('#skF_2',C_16),k1_xboole_0)
      | ~ r2_hidden(C_16,'#skF_3')
      | ~ m1_subset_1(C_16,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_943])).

tff(c_1020,plain,(
    ! [C_112] :
      ( ~ r2_hidden(C_112,'#skF_3')
      | ~ m1_subset_1(C_112,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_960])).

tff(c_1061,plain,(
    ! [A_115] : ~ r2_hidden(A_115,'#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_1020])).

tff(c_1065,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_1061])).

tff(c_1069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1065])).

tff(c_1071,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_169,plain,(
    ! [A_66,B_67] :
      ( k6_setfam_1(A_66,k7_setfam_1(A_66,B_67)) = k3_subset_1(A_66,k5_setfam_1(A_66,B_67))
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1273,plain,(
    ! [A_124,B_125] :
      ( k6_setfam_1(A_124,k7_setfam_1(A_124,k7_setfam_1(A_124,B_125))) = k3_subset_1(A_124,k5_setfam_1(A_124,k7_setfam_1(A_124,B_125)))
      | k7_setfam_1(A_124,B_125) = k1_xboole_0
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k1_zfmisc_1(A_124))) ) ),
    inference(resolution,[status(thm)],[c_14,c_169])).

tff(c_1288,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1273])).

tff(c_1297,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_1288])).

tff(c_1298,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1071,c_1297])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k5_setfam_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_142,plain,(
    ! [A_60,B_61] :
      ( k3_subset_1(A_60,k3_subset_1(A_60,k5_setfam_1(A_60,B_61))) = k5_setfam_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(resolution,[status(thm)],[c_136,c_10])).

tff(c_360,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_341,c_142])).

tff(c_1342,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_360])).

tff(c_1343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n009.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 19:41:56 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.43  
% 3.20/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.43  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_tarski > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.20/1.43  
% 3.20/1.43  %Foreground sorts:
% 3.20/1.43  
% 3.20/1.43  
% 3.20/1.43  %Background operators:
% 3.20/1.43  
% 3.20/1.43  
% 3.20/1.43  %Foreground operators:
% 3.20/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.43  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.20/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.20/1.43  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.43  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.20/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.43  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.20/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.43  
% 3.20/1.45  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 3.20/1.45  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.20/1.45  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.20/1.45  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.20/1.45  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.20/1.45  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.20/1.45  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.20/1.45  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.20/1.45  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 3.20/1.45  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.20/1.45  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.20/1.45  tff(c_32, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.20/1.45  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.20/1.45  tff(c_24, plain, (![A_20]: (r2_hidden('#skF_1'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.20/1.45  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.20/1.45  tff(c_93, plain, (![A_42, C_43, B_44]: (m1_subset_1(A_42, C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.45  tff(c_96, plain, (![A_42]: (m1_subset_1(A_42, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_42, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_93])).
% 3.20/1.45  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.45  tff(c_59, plain, (![A_34, B_35]: (~r2_hidden(A_34, k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.20/1.45  tff(c_62, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 3.20/1.45  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k7_setfam_1(A_9, B_10), k1_zfmisc_1(k1_zfmisc_1(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.45  tff(c_143, plain, (![A_62, B_63]: (k7_setfam_1(A_62, k7_setfam_1(A_62, B_63))=B_63 | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.20/1.45  tff(c_150, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_143])).
% 3.20/1.45  tff(c_155, plain, (![A_64, B_65]: (m1_subset_1(k7_setfam_1(A_64, B_65), k1_zfmisc_1(k1_zfmisc_1(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.45  tff(c_22, plain, (![A_17, C_19, B_18]: (m1_subset_1(A_17, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.45  tff(c_191, plain, (![A_71, A_72, B_73]: (m1_subset_1(A_71, k1_zfmisc_1(A_72)) | ~r2_hidden(A_71, k7_setfam_1(A_72, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(resolution, [status(thm)], [c_155, c_22])).
% 3.20/1.45  tff(c_275, plain, (![A_83, B_84]: (m1_subset_1('#skF_1'(k7_setfam_1(A_83, B_84)), k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))) | k7_setfam_1(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_191])).
% 3.20/1.45  tff(c_294, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_150, c_275])).
% 3.20/1.45  tff(c_301, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_294])).
% 3.20/1.45  tff(c_302, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_301])).
% 3.20/1.45  tff(c_332, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_302])).
% 3.20/1.45  tff(c_335, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_332])).
% 3.20/1.45  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_335])).
% 3.20/1.45  tff(c_341, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_302])).
% 3.20/1.45  tff(c_892, plain, (![A_110]: (m1_subset_1(A_110, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_110, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_341, c_22])).
% 3.20/1.45  tff(c_904, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_892])).
% 3.20/1.45  tff(c_905, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_904])).
% 3.20/1.45  tff(c_18, plain, (![A_13, C_16, B_14]: (r2_hidden(k3_subset_1(A_13, C_16), k7_setfam_1(A_13, B_14)) | ~r2_hidden(C_16, B_14) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.45  tff(c_943, plain, (![C_16]: (r2_hidden(k3_subset_1('#skF_2', C_16), k1_xboole_0) | ~r2_hidden(C_16, '#skF_3') | ~m1_subset_1(C_16, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_905, c_18])).
% 3.20/1.45  tff(c_960, plain, (![C_16]: (r2_hidden(k3_subset_1('#skF_2', C_16), k1_xboole_0) | ~r2_hidden(C_16, '#skF_3') | ~m1_subset_1(C_16, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_943])).
% 3.20/1.45  tff(c_1020, plain, (![C_112]: (~r2_hidden(C_112, '#skF_3') | ~m1_subset_1(C_112, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_960])).
% 3.20/1.45  tff(c_1061, plain, (![A_115]: (~r2_hidden(A_115, '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_1020])).
% 3.20/1.45  tff(c_1065, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_24, c_1061])).
% 3.20/1.45  tff(c_1069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1065])).
% 3.20/1.45  tff(c_1071, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_904])).
% 3.20/1.45  tff(c_169, plain, (![A_66, B_67]: (k6_setfam_1(A_66, k7_setfam_1(A_66, B_67))=k3_subset_1(A_66, k5_setfam_1(A_66, B_67)) | k1_xboole_0=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.45  tff(c_1273, plain, (![A_124, B_125]: (k6_setfam_1(A_124, k7_setfam_1(A_124, k7_setfam_1(A_124, B_125)))=k3_subset_1(A_124, k5_setfam_1(A_124, k7_setfam_1(A_124, B_125))) | k7_setfam_1(A_124, B_125)=k1_xboole_0 | ~m1_subset_1(B_125, k1_zfmisc_1(k1_zfmisc_1(A_124))))), inference(resolution, [status(thm)], [c_14, c_169])).
% 3.20/1.45  tff(c_1288, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1273])).
% 3.20/1.45  tff(c_1297, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_1288])).
% 3.20/1.45  tff(c_1298, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1071, c_1297])).
% 3.20/1.45  tff(c_136, plain, (![A_60, B_61]: (m1_subset_1(k5_setfam_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.45  tff(c_10, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.45  tff(c_142, plain, (![A_60, B_61]: (k3_subset_1(A_60, k3_subset_1(A_60, k5_setfam_1(A_60, B_61)))=k5_setfam_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(resolution, [status(thm)], [c_136, c_10])).
% 3.20/1.45  tff(c_360, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_341, c_142])).
% 3.20/1.45  tff(c_1342, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_360])).
% 3.20/1.45  tff(c_1343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1342])).
% 3.20/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.45  
% 3.20/1.45  Inference rules
% 3.20/1.45  ----------------------
% 3.20/1.45  #Ref     : 0
% 3.20/1.45  #Sup     : 333
% 3.20/1.45  #Fact    : 0
% 3.20/1.45  #Define  : 0
% 3.20/1.45  #Split   : 9
% 3.20/1.45  #Chain   : 0
% 3.20/1.45  #Close   : 0
% 3.20/1.45  
% 3.20/1.45  Ordering : KBO
% 3.20/1.45  
% 3.20/1.45  Simplification rules
% 3.20/1.45  ----------------------
% 3.20/1.45  #Subsume      : 43
% 3.20/1.45  #Demod        : 136
% 3.20/1.45  #Tautology    : 122
% 3.20/1.45  #SimpNegUnit  : 45
% 3.20/1.45  #BackRed      : 21
% 3.20/1.45  
% 3.20/1.45  #Partial instantiations: 0
% 3.20/1.45  #Strategies tried      : 1
% 3.20/1.45  
% 3.20/1.45  Timing (in seconds)
% 3.20/1.45  ----------------------
% 3.20/1.45  Preprocessing        : 0.32
% 3.20/1.45  Parsing              : 0.18
% 3.53/1.45  CNF conversion       : 0.02
% 3.53/1.45  Main loop            : 0.47
% 3.53/1.45  Inferencing          : 0.16
% 3.53/1.45  Reduction            : 0.15
% 3.53/1.45  Demodulation         : 0.10
% 3.53/1.45  BG Simplification    : 0.02
% 3.53/1.45  Subsumption          : 0.10
% 3.53/1.45  Abstraction          : 0.03
% 3.53/1.45  MUC search           : 0.00
% 3.53/1.45  Cooper               : 0.00
% 3.53/1.45  Total                : 0.83
% 3.53/1.45  Index Insertion      : 0.00
% 3.53/1.45  Index Deletion       : 0.00
% 3.53/1.45  Index Matching       : 0.00
% 3.53/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
