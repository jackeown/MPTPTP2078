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
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 184 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  113 ( 364 expanded)
%              Number of equality atoms :   37 ( 129 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

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

tff(c_92,plain,(
    ! [A_50,C_51,B_52] :
      ( m1_subset_1(A_50,C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,(
    ! [A_50] :
      ( m1_subset_1(A_50,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_50,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_92])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [B_43,A_44] :
      ( ~ r2_hidden(B_43,A_44)
      | k4_xboole_0(A_44,k1_tarski(B_43)) != A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [B_43] : ~ r2_hidden(B_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k7_setfam_1(A_10,B_11),k1_zfmisc_1(k1_zfmisc_1(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_116,plain,(
    ! [A_59,B_60] :
      ( k7_setfam_1(A_59,k7_setfam_1(A_59,B_60)) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_152,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k7_setfam_1(A_64,B_65),k1_zfmisc_1(k1_zfmisc_1(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_18,C_20,B_19] :
      ( m1_subset_1(A_18,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,(
    ! [A_89,A_90,B_91] :
      ( m1_subset_1(A_89,k1_zfmisc_1(A_90))
      | ~ r2_hidden(A_89,k7_setfam_1(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(resolution,[status(thm)],[c_152,c_22])).

tff(c_282,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_101,B_102)),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(A_101)))
      | k7_setfam_1(A_101,B_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_198])).

tff(c_301,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_282])).

tff(c_308,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_301])).

tff(c_309,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_308])).

tff(c_310,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_342,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_310])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_342])).

tff(c_348,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_1235,plain,(
    ! [A_163] :
      ( m1_subset_1(A_163,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_163,k7_setfam_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_348,c_22])).

tff(c_1240,plain,
    ( m1_subset_1('#skF_1'(k7_setfam_1('#skF_2','#skF_3')),k1_zfmisc_1('#skF_2'))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_1235])).

tff(c_1241,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1240])).

tff(c_1272,plain,(
    ! [A_164,C_165,B_166] :
      ( r2_hidden(k3_subset_1(A_164,C_165),k7_setfam_1(A_164,B_166))
      | ~ r2_hidden(C_165,B_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(A_164))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k1_zfmisc_1(A_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1286,plain,(
    ! [C_165] :
      ( r2_hidden(k3_subset_1('#skF_2',C_165),k1_xboole_0)
      | ~ r2_hidden(C_165,'#skF_3')
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_1272])).

tff(c_1305,plain,(
    ! [C_165] :
      ( r2_hidden(k3_subset_1('#skF_2',C_165),k1_xboole_0)
      | ~ r2_hidden(C_165,'#skF_3')
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1286])).

tff(c_1352,plain,(
    ! [C_167] :
      ( ~ r2_hidden(C_167,'#skF_3')
      | ~ m1_subset_1(C_167,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1305])).

tff(c_1376,plain,(
    ! [A_168] : ~ r2_hidden(A_168,'#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_1352])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_1376])).

tff(c_1384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1380])).

tff(c_1386,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1240])).

tff(c_181,plain,(
    ! [A_87,B_88] :
      ( k6_setfam_1(A_87,k7_setfam_1(A_87,B_88)) = k3_subset_1(A_87,k5_setfam_1(A_87,B_88))
      | k1_xboole_0 = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(A_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1668,plain,(
    ! [A_185,B_186] :
      ( k6_setfam_1(A_185,k7_setfam_1(A_185,k7_setfam_1(A_185,B_186))) = k3_subset_1(A_185,k5_setfam_1(A_185,k7_setfam_1(A_185,B_186)))
      | k7_setfam_1(A_185,B_186) = k1_xboole_0
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k1_zfmisc_1(A_185))) ) ),
    inference(resolution,[status(thm)],[c_14,c_181])).

tff(c_1683,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1668])).

tff(c_1692,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_1683])).

tff(c_1693,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1386,c_1692])).

tff(c_141,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k5_setfam_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_subset_1(A_6,k3_subset_1(A_6,B_7)) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,(
    ! [A_62,B_63] :
      ( k3_subset_1(A_62,k3_subset_1(A_62,k5_setfam_1(A_62,B_63))) = k5_setfam_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(resolution,[status(thm)],[c_141,c_10])).

tff(c_367,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_348,c_150])).

tff(c_1866,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_367])).

tff(c_1867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.75  
% 4.06/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.75  %$ r2_hidden > m1_subset_1 > k4_mcart_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.06/1.75  
% 4.06/1.75  %Foreground sorts:
% 4.06/1.75  
% 4.06/1.75  
% 4.06/1.75  %Background operators:
% 4.06/1.75  
% 4.06/1.75  
% 4.06/1.75  %Foreground operators:
% 4.06/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.06/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.06/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.06/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.75  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.06/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.06/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.06/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.06/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.06/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.75  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.06/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.75  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.06/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.06/1.75  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.06/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.75  
% 4.06/1.77  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.06/1.77  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 4.06/1.77  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.06/1.77  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.06/1.77  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.06/1.77  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.06/1.77  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.06/1.77  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 4.06/1.77  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.06/1.77  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.06/1.77  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.06/1.77  tff(c_32, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.06/1.77  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.06/1.77  tff(c_24, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.06/1.77  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.06/1.77  tff(c_92, plain, (![A_50, C_51, B_52]: (m1_subset_1(A_50, C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.77  tff(c_95, plain, (![A_50]: (m1_subset_1(A_50, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_50, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_92])).
% 4.06/1.77  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.06/1.77  tff(c_45, plain, (![B_43, A_44]: (~r2_hidden(B_43, A_44) | k4_xboole_0(A_44, k1_tarski(B_43))!=A_44)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.06/1.77  tff(c_50, plain, (![B_43]: (~r2_hidden(B_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45])).
% 4.06/1.77  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k7_setfam_1(A_10, B_11), k1_zfmisc_1(k1_zfmisc_1(A_10))) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.06/1.77  tff(c_116, plain, (![A_59, B_60]: (k7_setfam_1(A_59, k7_setfam_1(A_59, B_60))=B_60 | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.77  tff(c_119, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_116])).
% 4.06/1.77  tff(c_152, plain, (![A_64, B_65]: (m1_subset_1(k7_setfam_1(A_64, B_65), k1_zfmisc_1(k1_zfmisc_1(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.06/1.77  tff(c_22, plain, (![A_18, C_20, B_19]: (m1_subset_1(A_18, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.77  tff(c_198, plain, (![A_89, A_90, B_91]: (m1_subset_1(A_89, k1_zfmisc_1(A_90)) | ~r2_hidden(A_89, k7_setfam_1(A_90, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(resolution, [status(thm)], [c_152, c_22])).
% 4.06/1.77  tff(c_282, plain, (![A_101, B_102]: (m1_subset_1('#skF_1'(k7_setfam_1(A_101, B_102)), k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(A_101))) | k7_setfam_1(A_101, B_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_198])).
% 4.06/1.77  tff(c_301, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_119, c_282])).
% 4.06/1.77  tff(c_308, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_301])).
% 4.06/1.77  tff(c_309, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_308])).
% 4.06/1.77  tff(c_310, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_309])).
% 4.06/1.77  tff(c_342, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_310])).
% 4.06/1.77  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_342])).
% 4.06/1.77  tff(c_348, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_309])).
% 4.06/1.77  tff(c_1235, plain, (![A_163]: (m1_subset_1(A_163, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_163, k7_setfam_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_348, c_22])).
% 4.06/1.77  tff(c_1240, plain, (m1_subset_1('#skF_1'(k7_setfam_1('#skF_2', '#skF_3')), k1_zfmisc_1('#skF_2')) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_1235])).
% 4.06/1.77  tff(c_1241, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1240])).
% 4.06/1.77  tff(c_1272, plain, (![A_164, C_165, B_166]: (r2_hidden(k3_subset_1(A_164, C_165), k7_setfam_1(A_164, B_166)) | ~r2_hidden(C_165, B_166) | ~m1_subset_1(C_165, k1_zfmisc_1(A_164)) | ~m1_subset_1(B_166, k1_zfmisc_1(k1_zfmisc_1(A_164))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.06/1.77  tff(c_1286, plain, (![C_165]: (r2_hidden(k3_subset_1('#skF_2', C_165), k1_xboole_0) | ~r2_hidden(C_165, '#skF_3') | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_1272])).
% 4.06/1.77  tff(c_1305, plain, (![C_165]: (r2_hidden(k3_subset_1('#skF_2', C_165), k1_xboole_0) | ~r2_hidden(C_165, '#skF_3') | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1286])).
% 4.06/1.77  tff(c_1352, plain, (![C_167]: (~r2_hidden(C_167, '#skF_3') | ~m1_subset_1(C_167, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1305])).
% 4.06/1.77  tff(c_1376, plain, (![A_168]: (~r2_hidden(A_168, '#skF_3'))), inference(resolution, [status(thm)], [c_95, c_1352])).
% 4.06/1.77  tff(c_1380, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_24, c_1376])).
% 4.06/1.77  tff(c_1384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1380])).
% 4.42/1.77  tff(c_1386, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1240])).
% 4.42/1.77  tff(c_181, plain, (![A_87, B_88]: (k6_setfam_1(A_87, k7_setfam_1(A_87, B_88))=k3_subset_1(A_87, k5_setfam_1(A_87, B_88)) | k1_xboole_0=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(A_87))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.42/1.77  tff(c_1668, plain, (![A_185, B_186]: (k6_setfam_1(A_185, k7_setfam_1(A_185, k7_setfam_1(A_185, B_186)))=k3_subset_1(A_185, k5_setfam_1(A_185, k7_setfam_1(A_185, B_186))) | k7_setfam_1(A_185, B_186)=k1_xboole_0 | ~m1_subset_1(B_186, k1_zfmisc_1(k1_zfmisc_1(A_185))))), inference(resolution, [status(thm)], [c_14, c_181])).
% 4.42/1.77  tff(c_1683, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1668])).
% 4.42/1.77  tff(c_1692, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_1683])).
% 4.42/1.77  tff(c_1693, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1386, c_1692])).
% 4.42/1.77  tff(c_141, plain, (![A_62, B_63]: (m1_subset_1(k5_setfam_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.42/1.77  tff(c_10, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, B_7))=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.42/1.77  tff(c_150, plain, (![A_62, B_63]: (k3_subset_1(A_62, k3_subset_1(A_62, k5_setfam_1(A_62, B_63)))=k5_setfam_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(resolution, [status(thm)], [c_141, c_10])).
% 4.42/1.77  tff(c_367, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_348, c_150])).
% 4.42/1.77  tff(c_1866, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_367])).
% 4.42/1.77  tff(c_1867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1866])).
% 4.42/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.77  
% 4.42/1.77  Inference rules
% 4.42/1.77  ----------------------
% 4.42/1.77  #Ref     : 0
% 4.42/1.77  #Sup     : 453
% 4.42/1.77  #Fact    : 0
% 4.42/1.77  #Define  : 0
% 4.42/1.77  #Split   : 21
% 4.42/1.77  #Chain   : 0
% 4.42/1.77  #Close   : 0
% 4.42/1.77  
% 4.42/1.77  Ordering : KBO
% 4.42/1.77  
% 4.42/1.77  Simplification rules
% 4.42/1.77  ----------------------
% 4.42/1.77  #Subsume      : 68
% 4.42/1.77  #Demod        : 220
% 4.42/1.77  #Tautology    : 154
% 4.42/1.77  #SimpNegUnit  : 57
% 4.42/1.77  #BackRed      : 40
% 4.42/1.77  
% 4.42/1.77  #Partial instantiations: 0
% 4.42/1.77  #Strategies tried      : 1
% 4.42/1.77  
% 4.42/1.77  Timing (in seconds)
% 4.42/1.77  ----------------------
% 4.42/1.77  Preprocessing        : 0.32
% 4.42/1.77  Parsing              : 0.17
% 4.42/1.77  CNF conversion       : 0.02
% 4.42/1.77  Main loop            : 0.67
% 4.42/1.77  Inferencing          : 0.22
% 4.42/1.77  Reduction            : 0.21
% 4.42/1.77  Demodulation         : 0.14
% 4.42/1.78  BG Simplification    : 0.03
% 4.42/1.78  Subsumption          : 0.15
% 4.42/1.78  Abstraction          : 0.04
% 4.42/1.78  MUC search           : 0.00
% 4.42/1.78  Cooper               : 0.00
% 4.42/1.78  Total                : 1.03
% 4.42/1.78  Index Insertion      : 0.00
% 4.42/1.78  Index Deletion       : 0.00
% 4.42/1.78  Index Matching       : 0.00
% 4.42/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
