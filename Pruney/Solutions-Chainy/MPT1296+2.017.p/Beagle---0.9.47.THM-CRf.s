%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 184 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  113 ( 364 expanded)
%              Number of equality atoms :   37 ( 129 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

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
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_105,plain,(
    ! [A_49,C_50,B_51] :
      ( m1_subset_1(A_49,C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    ! [A_49] :
      ( m1_subset_1(A_49,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | k4_xboole_0(A_36,k1_tarski(B_35)) != A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [B_35] : ~ r2_hidden(B_35,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k7_setfam_1(A_10,B_11),k1_zfmisc_1(k1_zfmisc_1(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_150,plain,(
    ! [A_64,B_65] :
      ( k7_setfam_1(A_64,k7_setfam_1(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_162,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k7_setfam_1(A_66,B_67),k1_zfmisc_1(k1_zfmisc_1(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_18,C_20,B_19] :
      ( m1_subset_1(A_18,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,(
    ! [A_73,A_74,B_75] :
      ( m1_subset_1(A_73,k1_zfmisc_1(A_74))
      | ~ r2_hidden(A_73,k7_setfam_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(resolution,[status(thm)],[c_162,c_22])).

tff(c_269,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_82,B_83)),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82)))
      | k7_setfam_1(A_82,B_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_198])).

tff(c_288,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_269])).

tff(c_295,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_288])).

tff(c_296,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_295])).

tff(c_297,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_300,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_297])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_300])).

tff(c_306,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_1223,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_130,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_306,c_22])).

tff(c_1235,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_1223])).

tff(c_1241,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1235])).

tff(c_18,plain,(
    ! [A_14,C_17,B_15] :
      ( r2_hidden(k3_subset_1(A_14,C_17),k7_setfam_1(A_14,B_15))
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1252,plain,(
    ! [C_17] :
      ( r2_hidden(k3_subset_1('#skF_2',C_17),k1_xboole_0)
      | ~ r2_hidden(C_17,'#skF_3')
      | ~ m1_subset_1(C_17,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_18])).

tff(c_1267,plain,(
    ! [C_17] :
      ( r2_hidden(k3_subset_1('#skF_2',C_17),k1_xboole_0)
      | ~ r2_hidden(C_17,'#skF_3')
      | ~ m1_subset_1(C_17,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1252])).

tff(c_1347,plain,(
    ! [C_133] :
      ( ~ r2_hidden(C_133,'#skF_3')
      | ~ m1_subset_1(C_133,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1267])).

tff(c_1371,plain,(
    ! [A_134] : ~ r2_hidden(A_134,'#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_1347])).

tff(c_1375,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_1371])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1375])).

tff(c_1381,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1235])).

tff(c_181,plain,(
    ! [A_71,B_72] :
      ( k6_setfam_1(A_71,k7_setfam_1(A_71,B_72)) = k3_subset_1(A_71,k5_setfam_1(A_71,B_72))
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1768,plain,(
    ! [A_149,B_150] :
      ( k6_setfam_1(A_149,k7_setfam_1(A_149,k7_setfam_1(A_149,B_150))) = k3_subset_1(A_149,k5_setfam_1(A_149,k7_setfam_1(A_149,B_150)))
      | k7_setfam_1(A_149,B_150) = k1_xboole_0
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_zfmisc_1(A_149))) ) ),
    inference(resolution,[status(thm)],[c_14,c_181])).

tff(c_1783,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1768])).

tff(c_1792,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1783])).

tff(c_1793,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1381,c_1792])).

tff(c_143,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k5_setfam_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_subset_1(A_6,k3_subset_1(A_6,B_7)) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_62,B_63] :
      ( k3_subset_1(A_62,k3_subset_1(A_62,k5_setfam_1(A_62,B_63))) = k5_setfam_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(resolution,[status(thm)],[c_143,c_10])).

tff(c_340,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_306,c_149])).

tff(c_1865,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_340])).

tff(c_1866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.66  
% 3.91/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.66  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.91/1.66  
% 3.91/1.66  %Foreground sorts:
% 3.91/1.66  
% 3.91/1.66  
% 3.91/1.66  %Background operators:
% 3.91/1.66  
% 3.91/1.66  
% 3.91/1.66  %Foreground operators:
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.91/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.91/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.66  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.91/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.91/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.91/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.66  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.66  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.66  
% 4.04/1.68  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.04/1.68  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.04/1.68  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.04/1.68  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.04/1.68  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.04/1.68  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.04/1.68  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.04/1.68  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 4.04/1.68  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.04/1.68  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.04/1.68  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.04/1.68  tff(c_32, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.04/1.68  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.04/1.68  tff(c_24, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.04/1.68  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.04/1.68  tff(c_105, plain, (![A_49, C_50, B_51]: (m1_subset_1(A_49, C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.04/1.68  tff(c_108, plain, (![A_49]: (m1_subset_1(A_49, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_105])).
% 4.04/1.68  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.04/1.68  tff(c_45, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | k4_xboole_0(A_36, k1_tarski(B_35))!=A_36)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.04/1.68  tff(c_50, plain, (![B_35]: (~r2_hidden(B_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45])).
% 4.04/1.68  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k7_setfam_1(A_10, B_11), k1_zfmisc_1(k1_zfmisc_1(A_10))) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.04/1.68  tff(c_150, plain, (![A_64, B_65]: (k7_setfam_1(A_64, k7_setfam_1(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.04/1.68  tff(c_157, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_150])).
% 4.04/1.68  tff(c_162, plain, (![A_66, B_67]: (m1_subset_1(k7_setfam_1(A_66, B_67), k1_zfmisc_1(k1_zfmisc_1(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.04/1.68  tff(c_22, plain, (![A_18, C_20, B_19]: (m1_subset_1(A_18, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.04/1.68  tff(c_198, plain, (![A_73, A_74, B_75]: (m1_subset_1(A_73, k1_zfmisc_1(A_74)) | ~r2_hidden(A_73, k7_setfam_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(resolution, [status(thm)], [c_162, c_22])).
% 4.04/1.68  tff(c_269, plain, (![A_82, B_83]: (m1_subset_1('#skF_1'(k7_setfam_1(A_82, B_83)), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))) | k7_setfam_1(A_82, B_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_198])).
% 4.04/1.68  tff(c_288, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_157, c_269])).
% 4.04/1.68  tff(c_295, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_288])).
% 4.04/1.68  tff(c_296, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_295])).
% 4.04/1.68  tff(c_297, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_296])).
% 4.04/1.68  tff(c_300, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_297])).
% 4.04/1.68  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_300])).
% 4.04/1.68  tff(c_306, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_296])).
% 4.04/1.68  tff(c_1223, plain, (![A_130]: (m1_subset_1(A_130, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_130, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_306, c_22])).
% 4.04/1.68  tff(c_1235, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_1223])).
% 4.04/1.68  tff(c_1241, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1235])).
% 4.04/1.68  tff(c_18, plain, (![A_14, C_17, B_15]: (r2_hidden(k3_subset_1(A_14, C_17), k7_setfam_1(A_14, B_15)) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.04/1.68  tff(c_1252, plain, (![C_17]: (r2_hidden(k3_subset_1('#skF_2', C_17), k1_xboole_0) | ~r2_hidden(C_17, '#skF_3') | ~m1_subset_1(C_17, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_18])).
% 4.04/1.68  tff(c_1267, plain, (![C_17]: (r2_hidden(k3_subset_1('#skF_2', C_17), k1_xboole_0) | ~r2_hidden(C_17, '#skF_3') | ~m1_subset_1(C_17, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1252])).
% 4.04/1.68  tff(c_1347, plain, (![C_133]: (~r2_hidden(C_133, '#skF_3') | ~m1_subset_1(C_133, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1267])).
% 4.04/1.68  tff(c_1371, plain, (![A_134]: (~r2_hidden(A_134, '#skF_3'))), inference(resolution, [status(thm)], [c_108, c_1347])).
% 4.04/1.68  tff(c_1375, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_24, c_1371])).
% 4.04/1.68  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1375])).
% 4.04/1.68  tff(c_1381, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1235])).
% 4.04/1.68  tff(c_181, plain, (![A_71, B_72]: (k6_setfam_1(A_71, k7_setfam_1(A_71, B_72))=k3_subset_1(A_71, k5_setfam_1(A_71, B_72)) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.68  tff(c_1768, plain, (![A_149, B_150]: (k6_setfam_1(A_149, k7_setfam_1(A_149, k7_setfam_1(A_149, B_150)))=k3_subset_1(A_149, k5_setfam_1(A_149, k7_setfam_1(A_149, B_150))) | k7_setfam_1(A_149, B_150)=k1_xboole_0 | ~m1_subset_1(B_150, k1_zfmisc_1(k1_zfmisc_1(A_149))))), inference(resolution, [status(thm)], [c_14, c_181])).
% 4.04/1.68  tff(c_1783, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1768])).
% 4.04/1.68  tff(c_1792, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1783])).
% 4.04/1.68  tff(c_1793, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1381, c_1792])).
% 4.04/1.68  tff(c_143, plain, (![A_62, B_63]: (m1_subset_1(k5_setfam_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.68  tff(c_10, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, B_7))=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.04/1.68  tff(c_149, plain, (![A_62, B_63]: (k3_subset_1(A_62, k3_subset_1(A_62, k5_setfam_1(A_62, B_63)))=k5_setfam_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(resolution, [status(thm)], [c_143, c_10])).
% 4.04/1.68  tff(c_340, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_306, c_149])).
% 4.04/1.68  tff(c_1865, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1793, c_340])).
% 4.04/1.68  tff(c_1866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1865])).
% 4.04/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.68  
% 4.04/1.68  Inference rules
% 4.04/1.68  ----------------------
% 4.04/1.68  #Ref     : 0
% 4.04/1.68  #Sup     : 450
% 4.04/1.68  #Fact    : 0
% 4.04/1.68  #Define  : 0
% 4.04/1.68  #Split   : 19
% 4.04/1.68  #Chain   : 0
% 4.04/1.68  #Close   : 0
% 4.04/1.68  
% 4.04/1.68  Ordering : KBO
% 4.04/1.68  
% 4.04/1.68  Simplification rules
% 4.04/1.68  ----------------------
% 4.04/1.68  #Subsume      : 68
% 4.04/1.68  #Demod        : 236
% 4.04/1.68  #Tautology    : 158
% 4.04/1.68  #SimpNegUnit  : 57
% 4.04/1.68  #BackRed      : 40
% 4.04/1.68  
% 4.04/1.68  #Partial instantiations: 0
% 4.04/1.68  #Strategies tried      : 1
% 4.04/1.68  
% 4.04/1.68  Timing (in seconds)
% 4.04/1.68  ----------------------
% 4.04/1.68  Preprocessing        : 0.31
% 4.04/1.68  Parsing              : 0.17
% 4.04/1.68  CNF conversion       : 0.02
% 4.04/1.68  Main loop            : 0.60
% 4.04/1.68  Inferencing          : 0.20
% 4.04/1.68  Reduction            : 0.19
% 4.04/1.68  Demodulation         : 0.13
% 4.04/1.68  BG Simplification    : 0.03
% 4.04/1.68  Subsumption          : 0.13
% 4.04/1.68  Abstraction          : 0.03
% 4.04/1.68  MUC search           : 0.00
% 4.04/1.68  Cooper               : 0.00
% 4.04/1.68  Total                : 0.94
% 4.04/1.68  Index Insertion      : 0.00
% 4.04/1.68  Index Deletion       : 0.00
% 4.04/1.68  Index Matching       : 0.00
% 4.04/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
