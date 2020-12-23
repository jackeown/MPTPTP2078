%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 199 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 431 expanded)
%              Number of equality atoms :   30 ( 132 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_86,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_28,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_1'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    ! [A_50,C_51,B_52] :
      ( m1_subset_1(A_50,C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [A_50] :
      ( m1_subset_1(A_50,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_50,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k7_setfam_1(A_7,B_8),k1_zfmisc_1(k1_zfmisc_1(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_62,B_63] :
      ( k7_setfam_1(A_62,k7_setfam_1(A_62,B_63)) = B_63
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_153,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k7_setfam_1(A_68,B_69),k1_zfmisc_1(k1_zfmisc_1(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( m1_subset_1(A_15,C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,(
    ! [A_73,A_74,B_75] :
      ( m1_subset_1(A_73,k1_zfmisc_1(A_74))
      | ~ r2_hidden(A_73,k7_setfam_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_326,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_88,B_89)),k1_zfmisc_1(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88)))
      | k7_setfam_1(A_88,B_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_176])).

tff(c_348,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_326])).

tff(c_356,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_348])).

tff(c_357,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_356])).

tff(c_358,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_361,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_10,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_361])).

tff(c_367,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_1609,plain,(
    ! [A_152] :
      ( m1_subset_1(A_152,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_152,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_367,c_18])).

tff(c_1621,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_1609])).

tff(c_1646,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1621])).

tff(c_368,plain,(
    ! [A_90,C_91,B_92] :
      ( r2_hidden(k3_subset_1(A_90,C_91),k7_setfam_1(A_90,B_92))
      | ~ r2_hidden(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1934,plain,(
    ! [A_161,B_162,C_163] :
      ( ~ r1_tarski(k7_setfam_1(A_161,B_162),k3_subset_1(A_161,C_163))
      | ~ r2_hidden(C_163,B_162)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k1_zfmisc_1(A_161))) ) ),
    inference(resolution,[status(thm)],[c_368,c_20])).

tff(c_1943,plain,(
    ! [C_163] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_2',C_163))
      | ~ r2_hidden(C_163,'#skF_3')
      | ~ m1_subset_1(C_163,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_1934])).

tff(c_1978,plain,(
    ! [C_164] :
      ( ~ r2_hidden(C_164,'#skF_3')
      | ~ m1_subset_1(C_164,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_1943])).

tff(c_2008,plain,(
    ! [A_165] : ~ r2_hidden(A_165,'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_1978])).

tff(c_2012,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_2008])).

tff(c_2016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2012])).

tff(c_2018,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1621])).

tff(c_26,plain,(
    ! [A_42,B_43] :
      ( k6_setfam_1(A_42,k7_setfam_1(A_42,B_43)) = k3_subset_1(A_42,k5_setfam_1(A_42,B_43))
      | k1_xboole_0 = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_413,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_367,c_26])).

tff(c_424,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_413])).

tff(c_2380,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2018,c_424])).

tff(c_142,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k5_setfam_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k3_subset_1(A_2,k3_subset_1(A_2,B_3)) = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [A_66,B_67] :
      ( k3_subset_1(A_66,k3_subset_1(A_66,k5_setfam_1(A_66,B_67))) = k5_setfam_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_422,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_367,c_151])).

tff(c_2407,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2380,c_422])).

tff(c_2408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.77  
% 4.23/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.23/1.77  
% 4.23/1.77  %Foreground sorts:
% 4.23/1.77  
% 4.23/1.77  
% 4.23/1.77  %Background operators:
% 4.23/1.77  
% 4.23/1.77  
% 4.23/1.77  %Foreground operators:
% 4.23/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.23/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.77  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.23/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.77  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.23/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.23/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.77  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.23/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.77  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.23/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.77  
% 4.23/1.79  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.23/1.79  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.23/1.79  tff(f_60, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.23/1.79  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.23/1.79  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.23/1.79  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.23/1.79  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 4.23/1.79  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.23/1.79  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.23/1.79  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.23/1.79  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.23/1.79  tff(c_28, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.23/1.79  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.23/1.79  tff(c_24, plain, (![A_20]: (r2_hidden('#skF_1'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.23/1.79  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.23/1.79  tff(c_48, plain, (![A_50, C_51, B_52]: (m1_subset_1(A_50, C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.23/1.79  tff(c_53, plain, (![A_50]: (m1_subset_1(A_50, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_50, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_48])).
% 4.23/1.79  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.79  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k7_setfam_1(A_7, B_8), k1_zfmisc_1(k1_zfmisc_1(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.23/1.79  tff(c_87, plain, (![A_62, B_63]: (k7_setfam_1(A_62, k7_setfam_1(A_62, B_63))=B_63 | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.23/1.79  tff(c_93, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_87])).
% 4.23/1.79  tff(c_153, plain, (![A_68, B_69]: (m1_subset_1(k7_setfam_1(A_68, B_69), k1_zfmisc_1(k1_zfmisc_1(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.23/1.79  tff(c_18, plain, (![A_15, C_17, B_16]: (m1_subset_1(A_15, C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.23/1.79  tff(c_176, plain, (![A_73, A_74, B_75]: (m1_subset_1(A_73, k1_zfmisc_1(A_74)) | ~r2_hidden(A_73, k7_setfam_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(resolution, [status(thm)], [c_153, c_18])).
% 4.23/1.79  tff(c_326, plain, (![A_88, B_89]: (m1_subset_1('#skF_1'(k7_setfam_1(A_88, B_89)), k1_zfmisc_1(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))) | k7_setfam_1(A_88, B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_176])).
% 4.23/1.79  tff(c_348, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_326])).
% 4.23/1.79  tff(c_356, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_348])).
% 4.23/1.79  tff(c_357, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_356])).
% 4.23/1.79  tff(c_358, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_357])).
% 4.23/1.79  tff(c_361, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_358])).
% 4.23/1.79  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_361])).
% 4.23/1.79  tff(c_367, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_357])).
% 4.23/1.79  tff(c_1609, plain, (![A_152]: (m1_subset_1(A_152, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_152, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_367, c_18])).
% 4.23/1.79  tff(c_1621, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_1609])).
% 4.23/1.79  tff(c_1646, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1621])).
% 4.23/1.79  tff(c_368, plain, (![A_90, C_91, B_92]: (r2_hidden(k3_subset_1(A_90, C_91), k7_setfam_1(A_90, B_92)) | ~r2_hidden(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(A_90)) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.23/1.79  tff(c_20, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.23/1.79  tff(c_1934, plain, (![A_161, B_162, C_163]: (~r1_tarski(k7_setfam_1(A_161, B_162), k3_subset_1(A_161, C_163)) | ~r2_hidden(C_163, B_162) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | ~m1_subset_1(B_162, k1_zfmisc_1(k1_zfmisc_1(A_161))))), inference(resolution, [status(thm)], [c_368, c_20])).
% 4.23/1.79  tff(c_1943, plain, (![C_163]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_2', C_163)) | ~r2_hidden(C_163, '#skF_3') | ~m1_subset_1(C_163, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_1934])).
% 4.23/1.79  tff(c_1978, plain, (![C_164]: (~r2_hidden(C_164, '#skF_3') | ~m1_subset_1(C_164, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_1943])).
% 4.23/1.79  tff(c_2008, plain, (![A_165]: (~r2_hidden(A_165, '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_1978])).
% 4.23/1.79  tff(c_2012, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_24, c_2008])).
% 4.23/1.79  tff(c_2016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2012])).
% 4.23/1.79  tff(c_2018, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1621])).
% 4.23/1.79  tff(c_26, plain, (![A_42, B_43]: (k6_setfam_1(A_42, k7_setfam_1(A_42, B_43))=k3_subset_1(A_42, k5_setfam_1(A_42, B_43)) | k1_xboole_0=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.23/1.79  tff(c_413, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_367, c_26])).
% 4.23/1.79  tff(c_424, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_93, c_413])).
% 4.23/1.79  tff(c_2380, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2018, c_424])).
% 4.23/1.79  tff(c_142, plain, (![A_66, B_67]: (m1_subset_1(k5_setfam_1(A_66, B_67), k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.23/1.79  tff(c_4, plain, (![A_2, B_3]: (k3_subset_1(A_2, k3_subset_1(A_2, B_3))=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.79  tff(c_151, plain, (![A_66, B_67]: (k3_subset_1(A_66, k3_subset_1(A_66, k5_setfam_1(A_66, B_67)))=k5_setfam_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(resolution, [status(thm)], [c_142, c_4])).
% 4.23/1.79  tff(c_422, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_367, c_151])).
% 4.23/1.79  tff(c_2407, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2380, c_422])).
% 4.23/1.79  tff(c_2408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2407])).
% 4.23/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.79  
% 4.23/1.79  Inference rules
% 4.23/1.79  ----------------------
% 4.23/1.79  #Ref     : 0
% 4.23/1.79  #Sup     : 572
% 4.23/1.79  #Fact    : 0
% 4.23/1.79  #Define  : 0
% 4.23/1.79  #Split   : 25
% 4.23/1.79  #Chain   : 0
% 4.23/1.79  #Close   : 0
% 4.23/1.79  
% 4.23/1.79  Ordering : KBO
% 4.23/1.79  
% 4.23/1.79  Simplification rules
% 4.23/1.79  ----------------------
% 4.23/1.79  #Subsume      : 70
% 4.23/1.79  #Demod        : 292
% 4.23/1.79  #Tautology    : 199
% 4.23/1.79  #SimpNegUnit  : 38
% 4.23/1.79  #BackRed      : 51
% 4.23/1.79  
% 4.23/1.79  #Partial instantiations: 0
% 4.23/1.79  #Strategies tried      : 1
% 4.23/1.79  
% 4.23/1.79  Timing (in seconds)
% 4.23/1.79  ----------------------
% 4.23/1.79  Preprocessing        : 0.31
% 4.23/1.79  Parsing              : 0.17
% 4.23/1.79  CNF conversion       : 0.02
% 4.23/1.79  Main loop            : 0.71
% 4.23/1.79  Inferencing          : 0.23
% 4.23/1.79  Reduction            : 0.24
% 4.23/1.79  Demodulation         : 0.18
% 4.23/1.79  BG Simplification    : 0.03
% 4.23/1.79  Subsumption          : 0.14
% 4.23/1.79  Abstraction          : 0.03
% 4.23/1.79  MUC search           : 0.00
% 4.23/1.79  Cooper               : 0.00
% 4.23/1.79  Total                : 1.05
% 4.23/1.79  Index Insertion      : 0.00
% 4.23/1.79  Index Deletion       : 0.00
% 4.23/1.79  Index Matching       : 0.00
% 4.23/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
