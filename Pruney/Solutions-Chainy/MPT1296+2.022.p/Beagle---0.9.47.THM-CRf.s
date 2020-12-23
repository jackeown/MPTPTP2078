%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 180 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 364 expanded)
%              Number of equality atoms :   33 ( 125 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_35,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_1'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    ! [A_43,C_44,B_45] :
      ( m1_subset_1(A_43,C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k7_setfam_1(A_6,B_7),k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_56,B_57] :
      ( k7_setfam_1(A_56,k7_setfam_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_117,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k7_setfam_1(A_76,B_77),k1_zfmisc_1(k1_zfmisc_1(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( m1_subset_1(A_14,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [A_81,A_82,B_83] :
      ( m1_subset_1(A_81,k1_zfmisc_1(A_82))
      | ~ r2_hidden(A_81,k7_setfam_1(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_237,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_95,B_96)),k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k1_zfmisc_1(A_95)))
      | k7_setfam_1(A_95,B_96) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_256,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_237])).

tff(c_263,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_256])).

tff(c_264,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_263])).

tff(c_265,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_268,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_265])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_268])).

tff(c_274,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_1333,plain,(
    ! [A_163] :
      ( m1_subset_1(A_163,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_163,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_274,c_16])).

tff(c_1345,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1333])).

tff(c_1346,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1345])).

tff(c_281,plain,(
    ! [A_97,C_98,B_99] :
      ( r2_hidden(k3_subset_1(A_97,C_98),k7_setfam_1(A_97,B_99))
      | ~ r2_hidden(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1571,plain,(
    ! [A_174,B_175,C_176] :
      ( ~ r1_tarski(k7_setfam_1(A_174,B_175),k3_subset_1(A_174,C_176))
      | ~ r2_hidden(C_176,B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(A_174))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k1_zfmisc_1(A_174))) ) ),
    inference(resolution,[status(thm)],[c_281,c_18])).

tff(c_1589,plain,(
    ! [C_176] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_2',C_176))
      | ~ r2_hidden(C_176,'#skF_3')
      | ~ m1_subset_1(C_176,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_1571])).

tff(c_1606,plain,(
    ! [C_177] :
      ( ~ r2_hidden(C_177,'#skF_3')
      | ~ m1_subset_1(C_177,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_1589])).

tff(c_1634,plain,(
    ! [A_178] : ~ r2_hidden(A_178,'#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_1606])).

tff(c_1638,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_1634])).

tff(c_1642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1638])).

tff(c_1644,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1345])).

tff(c_154,plain,(
    ! [A_86,B_87] :
      ( k6_setfam_1(A_86,k7_setfam_1(A_86,B_87)) = k3_subset_1(A_86,k5_setfam_1(A_86,B_87))
      | k1_xboole_0 = B_87
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1895,plain,(
    ! [A_200,B_201] :
      ( k6_setfam_1(A_200,k7_setfam_1(A_200,k7_setfam_1(A_200,B_201))) = k3_subset_1(A_200,k5_setfam_1(A_200,k7_setfam_1(A_200,B_201)))
      | k7_setfam_1(A_200,B_201) = k1_xboole_0
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k1_zfmisc_1(A_200))) ) ),
    inference(resolution,[status(thm)],[c_8,c_154])).

tff(c_1910,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1895])).

tff(c_1919,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1910])).

tff(c_1920,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1644,c_1919])).

tff(c_88,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k5_setfam_1(A_54,B_55),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k3_subset_1(A_2,k3_subset_1(A_2,B_3)) = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_54,B_55] :
      ( k3_subset_1(A_54,k3_subset_1(A_54,k5_setfam_1(A_54,B_55))) = k5_setfam_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_330,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_274,c_93])).

tff(c_2111,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_330])).

tff(c_2112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.76  
% 3.95/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.76  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.95/1.76  
% 3.95/1.76  %Foreground sorts:
% 3.95/1.76  
% 3.95/1.76  
% 3.95/1.76  %Background operators:
% 3.95/1.76  
% 3.95/1.76  
% 3.95/1.76  %Foreground operators:
% 3.95/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.76  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.95/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.95/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.76  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.95/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.76  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.95/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.76  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.95/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.76  
% 4.31/1.79  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.31/1.79  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 4.31/1.79  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.31/1.79  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.31/1.79  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.31/1.79  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.31/1.79  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 4.31/1.79  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.31/1.79  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.31/1.79  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.31/1.79  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.31/1.79  tff(c_28, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.31/1.79  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.31/1.79  tff(c_20, plain, (![A_19]: (r2_hidden('#skF_1'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.31/1.79  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.31/1.79  tff(c_40, plain, (![A_43, C_44, B_45]: (m1_subset_1(A_43, C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.31/1.79  tff(c_43, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_43, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_40])).
% 4.31/1.79  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.31/1.79  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k7_setfam_1(A_6, B_7), k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.31/1.79  tff(c_95, plain, (![A_56, B_57]: (k7_setfam_1(A_56, k7_setfam_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.31/1.79  tff(c_102, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_95])).
% 4.31/1.79  tff(c_117, plain, (![A_76, B_77]: (m1_subset_1(k7_setfam_1(A_76, B_77), k1_zfmisc_1(k1_zfmisc_1(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.31/1.79  tff(c_16, plain, (![A_14, C_16, B_15]: (m1_subset_1(A_14, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.31/1.79  tff(c_136, plain, (![A_81, A_82, B_83]: (m1_subset_1(A_81, k1_zfmisc_1(A_82)) | ~r2_hidden(A_81, k7_setfam_1(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(resolution, [status(thm)], [c_117, c_16])).
% 4.31/1.79  tff(c_237, plain, (![A_95, B_96]: (m1_subset_1('#skF_1'(k7_setfam_1(A_95, B_96)), k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(k1_zfmisc_1(A_95))) | k7_setfam_1(A_95, B_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_136])).
% 4.31/1.79  tff(c_256, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_237])).
% 4.31/1.79  tff(c_263, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_256])).
% 4.31/1.79  tff(c_264, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_263])).
% 4.31/1.79  tff(c_265, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_264])).
% 4.31/1.79  tff(c_268, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_265])).
% 4.31/1.79  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_268])).
% 4.31/1.79  tff(c_274, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_264])).
% 4.31/1.79  tff(c_1333, plain, (![A_163]: (m1_subset_1(A_163, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_163, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_274, c_16])).
% 4.35/1.79  tff(c_1345, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_1333])).
% 4.35/1.79  tff(c_1346, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1345])).
% 4.35/1.79  tff(c_281, plain, (![A_97, C_98, B_99]: (r2_hidden(k3_subset_1(A_97, C_98), k7_setfam_1(A_97, B_99)) | ~r2_hidden(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.35/1.79  tff(c_18, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.35/1.79  tff(c_1571, plain, (![A_174, B_175, C_176]: (~r1_tarski(k7_setfam_1(A_174, B_175), k3_subset_1(A_174, C_176)) | ~r2_hidden(C_176, B_175) | ~m1_subset_1(C_176, k1_zfmisc_1(A_174)) | ~m1_subset_1(B_175, k1_zfmisc_1(k1_zfmisc_1(A_174))))), inference(resolution, [status(thm)], [c_281, c_18])).
% 4.35/1.79  tff(c_1589, plain, (![C_176]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_2', C_176)) | ~r2_hidden(C_176, '#skF_3') | ~m1_subset_1(C_176, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1346, c_1571])).
% 4.35/1.79  tff(c_1606, plain, (![C_177]: (~r2_hidden(C_177, '#skF_3') | ~m1_subset_1(C_177, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_1589])).
% 4.35/1.79  tff(c_1634, plain, (![A_178]: (~r2_hidden(A_178, '#skF_3'))), inference(resolution, [status(thm)], [c_43, c_1606])).
% 4.35/1.79  tff(c_1638, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_20, c_1634])).
% 4.35/1.79  tff(c_1642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1638])).
% 4.35/1.79  tff(c_1644, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1345])).
% 4.35/1.79  tff(c_154, plain, (![A_86, B_87]: (k6_setfam_1(A_86, k7_setfam_1(A_86, B_87))=k3_subset_1(A_86, k5_setfam_1(A_86, B_87)) | k1_xboole_0=B_87 | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_86))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.35/1.79  tff(c_1895, plain, (![A_200, B_201]: (k6_setfam_1(A_200, k7_setfam_1(A_200, k7_setfam_1(A_200, B_201)))=k3_subset_1(A_200, k5_setfam_1(A_200, k7_setfam_1(A_200, B_201))) | k7_setfam_1(A_200, B_201)=k1_xboole_0 | ~m1_subset_1(B_201, k1_zfmisc_1(k1_zfmisc_1(A_200))))), inference(resolution, [status(thm)], [c_8, c_154])).
% 4.35/1.79  tff(c_1910, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1895])).
% 4.35/1.79  tff(c_1919, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1910])).
% 4.35/1.79  tff(c_1920, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1644, c_1919])).
% 4.35/1.79  tff(c_88, plain, (![A_54, B_55]: (m1_subset_1(k5_setfam_1(A_54, B_55), k1_zfmisc_1(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.35/1.79  tff(c_4, plain, (![A_2, B_3]: (k3_subset_1(A_2, k3_subset_1(A_2, B_3))=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.79  tff(c_93, plain, (![A_54, B_55]: (k3_subset_1(A_54, k3_subset_1(A_54, k5_setfam_1(A_54, B_55)))=k5_setfam_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(resolution, [status(thm)], [c_88, c_4])).
% 4.35/1.79  tff(c_330, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_274, c_93])).
% 4.35/1.79  tff(c_2111, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_330])).
% 4.35/1.79  tff(c_2112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2111])).
% 4.35/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.79  
% 4.35/1.79  Inference rules
% 4.35/1.79  ----------------------
% 4.35/1.79  #Ref     : 0
% 4.35/1.79  #Sup     : 515
% 4.35/1.79  #Fact    : 0
% 4.35/1.79  #Define  : 0
% 4.35/1.79  #Split   : 18
% 4.35/1.79  #Chain   : 0
% 4.35/1.79  #Close   : 0
% 4.35/1.79  
% 4.35/1.79  Ordering : KBO
% 4.35/1.79  
% 4.35/1.79  Simplification rules
% 4.35/1.79  ----------------------
% 4.35/1.79  #Subsume      : 57
% 4.35/1.79  #Demod        : 255
% 4.35/1.79  #Tautology    : 161
% 4.35/1.79  #SimpNegUnit  : 50
% 4.35/1.79  #BackRed      : 40
% 4.35/1.79  
% 4.35/1.79  #Partial instantiations: 0
% 4.35/1.79  #Strategies tried      : 1
% 4.35/1.79  
% 4.35/1.79  Timing (in seconds)
% 4.35/1.79  ----------------------
% 4.35/1.79  Preprocessing        : 0.31
% 4.35/1.80  Parsing              : 0.16
% 4.35/1.80  CNF conversion       : 0.02
% 4.35/1.80  Main loop            : 0.69
% 4.35/1.80  Inferencing          : 0.23
% 4.35/1.80  Reduction            : 0.21
% 4.35/1.80  Demodulation         : 0.15
% 4.35/1.80  BG Simplification    : 0.03
% 4.35/1.80  Subsumption          : 0.16
% 4.35/1.80  Abstraction          : 0.04
% 4.35/1.80  MUC search           : 0.00
% 4.35/1.80  Cooper               : 0.00
% 4.35/1.80  Total                : 1.05
% 4.35/1.80  Index Insertion      : 0.00
% 4.35/1.80  Index Deletion       : 0.00
% 4.35/1.80  Index Matching       : 0.00
% 4.35/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
