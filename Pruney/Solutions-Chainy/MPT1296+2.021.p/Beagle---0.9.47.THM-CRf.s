%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 180 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 364 expanded)
%              Number of equality atoms :   33 ( 125 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

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
    ! [A_39,C_40,B_41] :
      ( m1_subset_1(A_39,C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ! [A_39] :
      ( m1_subset_1(A_39,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k7_setfam_1(A_6,B_7),k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_50,B_51] :
      ( k7_setfam_1(A_50,k7_setfam_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_117,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k7_setfam_1(A_68,B_69),k1_zfmisc_1(k1_zfmisc_1(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( m1_subset_1(A_14,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [A_73,A_74,B_75] :
      ( m1_subset_1(A_73,k1_zfmisc_1(A_74))
      | ~ r2_hidden(A_73,k7_setfam_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_253,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_87,B_88)),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_87)))
      | k7_setfam_1(A_87,B_88) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_272,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_253])).

tff(c_279,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_272])).

tff(c_280,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_279])).

tff(c_281,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_284,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_281])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_284])).

tff(c_290,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_1315,plain,(
    ! [A_151] :
      ( m1_subset_1(A_151,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_151,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_290,c_16])).

tff(c_1327,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1315])).

tff(c_1348,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_199,plain,(
    ! [A_82,C_83,B_84] :
      ( r2_hidden(k3_subset_1(A_82,C_83),k7_setfam_1(A_82,B_84))
      | ~ r2_hidden(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1641,plain,(
    ! [A_162,B_163,C_164] :
      ( ~ r1_tarski(k7_setfam_1(A_162,B_163),k3_subset_1(A_162,C_164))
      | ~ r2_hidden(C_164,B_163)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k1_zfmisc_1(A_162))) ) ),
    inference(resolution,[status(thm)],[c_199,c_18])).

tff(c_1662,plain,(
    ! [C_164] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_2',C_164))
      | ~ r2_hidden(C_164,'#skF_3')
      | ~ m1_subset_1(C_164,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1348,c_1641])).

tff(c_1679,plain,(
    ! [C_165] :
      ( ~ r2_hidden(C_165,'#skF_3')
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_1662])).

tff(c_1708,plain,(
    ! [A_166] : ~ r2_hidden(A_166,'#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_1679])).

tff(c_1712,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_1708])).

tff(c_1716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1712])).

tff(c_1718,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_154,plain,(
    ! [A_78,B_79] :
      ( k6_setfam_1(A_78,k7_setfam_1(A_78,B_79)) = k3_subset_1(A_78,k5_setfam_1(A_78,B_79))
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1985,plain,(
    ! [A_185,B_186] :
      ( k6_setfam_1(A_185,k7_setfam_1(A_185,k7_setfam_1(A_185,B_186))) = k3_subset_1(A_185,k5_setfam_1(A_185,k7_setfam_1(A_185,B_186)))
      | k7_setfam_1(A_185,B_186) = k1_xboole_0
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k1_zfmisc_1(A_185))) ) ),
    inference(resolution,[status(thm)],[c_8,c_154])).

tff(c_2000,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1985])).

tff(c_2009,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2000])).

tff(c_2010,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1718,c_2009])).

tff(c_92,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k5_setfam_1(A_52,B_53),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k3_subset_1(A_2,k3_subset_1(A_2,B_3)) = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_52,B_53] :
      ( k3_subset_1(A_52,k3_subset_1(A_52,k5_setfam_1(A_52,B_53))) = k5_setfam_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_330,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_290,c_101])).

tff(c_2352,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_330])).

tff(c_2353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.86  
% 4.20/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.86  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.20/1.86  
% 4.20/1.86  %Foreground sorts:
% 4.20/1.86  
% 4.20/1.86  
% 4.20/1.86  %Background operators:
% 4.20/1.86  
% 4.20/1.86  
% 4.20/1.86  %Foreground operators:
% 4.20/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.20/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.86  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.20/1.86  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.20/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.20/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.86  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.20/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.86  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.20/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.86  
% 4.20/1.89  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.20/1.89  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.20/1.89  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.20/1.89  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.20/1.89  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.20/1.89  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.20/1.89  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 4.20/1.89  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.20/1.89  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.20/1.89  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.20/1.89  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.20/1.89  tff(c_28, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.20/1.89  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.20/1.89  tff(c_20, plain, (![A_19]: (r2_hidden('#skF_1'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.20/1.89  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.20/1.89  tff(c_40, plain, (![A_39, C_40, B_41]: (m1_subset_1(A_39, C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.20/1.89  tff(c_43, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_40])).
% 4.20/1.89  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.89  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k7_setfam_1(A_6, B_7), k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.20/1.89  tff(c_88, plain, (![A_50, B_51]: (k7_setfam_1(A_50, k7_setfam_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.20/1.89  tff(c_91, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_88])).
% 4.20/1.89  tff(c_117, plain, (![A_68, B_69]: (m1_subset_1(k7_setfam_1(A_68, B_69), k1_zfmisc_1(k1_zfmisc_1(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.20/1.89  tff(c_16, plain, (![A_14, C_16, B_15]: (m1_subset_1(A_14, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.20/1.89  tff(c_136, plain, (![A_73, A_74, B_75]: (m1_subset_1(A_73, k1_zfmisc_1(A_74)) | ~r2_hidden(A_73, k7_setfam_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(resolution, [status(thm)], [c_117, c_16])).
% 4.20/1.89  tff(c_253, plain, (![A_87, B_88]: (m1_subset_1('#skF_1'(k7_setfam_1(A_87, B_88)), k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(A_87))) | k7_setfam_1(A_87, B_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_136])).
% 4.20/1.89  tff(c_272, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91, c_253])).
% 4.20/1.89  tff(c_279, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_272])).
% 4.20/1.89  tff(c_280, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_279])).
% 4.20/1.89  tff(c_281, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_280])).
% 4.20/1.89  tff(c_284, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_281])).
% 4.20/1.89  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_284])).
% 4.20/1.89  tff(c_290, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_280])).
% 4.20/1.89  tff(c_1315, plain, (![A_151]: (m1_subset_1(A_151, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_151, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_290, c_16])).
% 4.20/1.89  tff(c_1327, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_1315])).
% 4.20/1.89  tff(c_1348, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1327])).
% 4.20/1.89  tff(c_199, plain, (![A_82, C_83, B_84]: (r2_hidden(k3_subset_1(A_82, C_83), k7_setfam_1(A_82, B_84)) | ~r2_hidden(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(A_82)) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.20/1.89  tff(c_18, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.20/1.89  tff(c_1641, plain, (![A_162, B_163, C_164]: (~r1_tarski(k7_setfam_1(A_162, B_163), k3_subset_1(A_162, C_164)) | ~r2_hidden(C_164, B_163) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | ~m1_subset_1(B_163, k1_zfmisc_1(k1_zfmisc_1(A_162))))), inference(resolution, [status(thm)], [c_199, c_18])).
% 4.20/1.89  tff(c_1662, plain, (![C_164]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_2', C_164)) | ~r2_hidden(C_164, '#skF_3') | ~m1_subset_1(C_164, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1348, c_1641])).
% 4.20/1.89  tff(c_1679, plain, (![C_165]: (~r2_hidden(C_165, '#skF_3') | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_1662])).
% 4.20/1.89  tff(c_1708, plain, (![A_166]: (~r2_hidden(A_166, '#skF_3'))), inference(resolution, [status(thm)], [c_43, c_1679])).
% 4.20/1.89  tff(c_1712, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_20, c_1708])).
% 4.20/1.89  tff(c_1716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1712])).
% 4.20/1.89  tff(c_1718, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1327])).
% 4.20/1.89  tff(c_154, plain, (![A_78, B_79]: (k6_setfam_1(A_78, k7_setfam_1(A_78, B_79))=k3_subset_1(A_78, k5_setfam_1(A_78, B_79)) | k1_xboole_0=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.20/1.89  tff(c_1985, plain, (![A_185, B_186]: (k6_setfam_1(A_185, k7_setfam_1(A_185, k7_setfam_1(A_185, B_186)))=k3_subset_1(A_185, k5_setfam_1(A_185, k7_setfam_1(A_185, B_186))) | k7_setfam_1(A_185, B_186)=k1_xboole_0 | ~m1_subset_1(B_186, k1_zfmisc_1(k1_zfmisc_1(A_185))))), inference(resolution, [status(thm)], [c_8, c_154])).
% 4.20/1.89  tff(c_2000, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1985])).
% 4.20/1.89  tff(c_2009, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2000])).
% 4.20/1.89  tff(c_2010, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1718, c_2009])).
% 4.20/1.89  tff(c_92, plain, (![A_52, B_53]: (m1_subset_1(k5_setfam_1(A_52, B_53), k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.20/1.89  tff(c_4, plain, (![A_2, B_3]: (k3_subset_1(A_2, k3_subset_1(A_2, B_3))=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/1.89  tff(c_101, plain, (![A_52, B_53]: (k3_subset_1(A_52, k3_subset_1(A_52, k5_setfam_1(A_52, B_53)))=k5_setfam_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(resolution, [status(thm)], [c_92, c_4])).
% 4.20/1.89  tff(c_330, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_290, c_101])).
% 4.20/1.89  tff(c_2352, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_330])).
% 4.20/1.89  tff(c_2353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2352])).
% 4.20/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.89  
% 4.20/1.89  Inference rules
% 4.20/1.89  ----------------------
% 4.20/1.89  #Ref     : 0
% 4.20/1.89  #Sup     : 574
% 4.20/1.89  #Fact    : 0
% 4.20/1.89  #Define  : 0
% 4.20/1.89  #Split   : 18
% 4.20/1.89  #Chain   : 0
% 4.20/1.89  #Close   : 0
% 4.20/1.89  
% 4.20/1.89  Ordering : KBO
% 4.20/1.89  
% 4.20/1.89  Simplification rules
% 4.20/1.89  ----------------------
% 4.20/1.89  #Subsume      : 61
% 4.20/1.89  #Demod        : 287
% 4.20/1.89  #Tautology    : 177
% 4.20/1.89  #SimpNegUnit  : 54
% 4.20/1.89  #BackRed      : 39
% 4.20/1.89  
% 4.20/1.89  #Partial instantiations: 0
% 4.20/1.89  #Strategies tried      : 1
% 4.20/1.89  
% 4.20/1.89  Timing (in seconds)
% 4.20/1.89  ----------------------
% 4.66/1.90  Preprocessing        : 0.31
% 4.66/1.90  Parsing              : 0.16
% 4.66/1.90  CNF conversion       : 0.02
% 4.66/1.90  Main loop            : 0.79
% 4.66/1.90  Inferencing          : 0.26
% 4.66/1.90  Reduction            : 0.25
% 4.66/1.90  Demodulation         : 0.17
% 4.66/1.90  BG Simplification    : 0.04
% 4.66/1.90  Subsumption          : 0.17
% 4.66/1.90  Abstraction          : 0.04
% 4.66/1.90  MUC search           : 0.00
% 4.69/1.90  Cooper               : 0.00
% 4.69/1.90  Total                : 1.14
% 4.69/1.90  Index Insertion      : 0.00
% 4.69/1.90  Index Deletion       : 0.00
% 4.69/1.90  Index Matching       : 0.00
% 4.69/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
