%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 17.24s
% Output     : CNFRefutation 17.24s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 187 expanded)
%              Number of leaves         :   37 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  141 ( 379 expanded)
%              Number of equality atoms :   53 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_6 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_157,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_172,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_157])).

tff(c_175,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_172])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_291,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,B_89)
      | ~ r2_hidden(C_90,A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_502,plain,(
    ! [C_124,B_125,A_126] :
      ( ~ r2_hidden(C_124,B_125)
      | ~ r2_hidden(C_124,A_126)
      | k4_xboole_0(A_126,B_125) != A_126 ) ),
    inference(resolution,[status(thm)],[c_26,c_291])).

tff(c_624,plain,(
    ! [A_139,A_140] :
      ( ~ r2_hidden('#skF_1'(A_139),A_140)
      | k4_xboole_0(A_140,A_139) != A_140
      | v1_xboole_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_4,c_502])).

tff(c_633,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_624])).

tff(c_644,plain,(
    ! [A_141] :
      ( k1_xboole_0 != A_141
      | v1_xboole_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_633])).

tff(c_56,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_664,plain,(
    k3_xboole_0('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_644,c_56])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [A_35] :
      ( k6_domain_1(A_35,'#skF_6'(A_35)) = A_35
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,(
    ! [A_35] :
      ( m1_subset_1('#skF_6'(A_35),A_35)
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_310,plain,(
    ! [A_94,B_95] :
      ( k6_domain_1(A_94,B_95) = k1_tarski(B_95)
      | ~ m1_subset_1(B_95,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2308,plain,(
    ! [A_2534] :
      ( k6_domain_1(A_2534,'#skF_6'(A_2534)) = k1_tarski('#skF_6'(A_2534))
      | ~ v1_zfmisc_1(A_2534)
      | v1_xboole_0(A_2534) ) ),
    inference(resolution,[status(thm)],[c_52,c_310])).

tff(c_4593,plain,(
    ! [A_2824] :
      ( k1_tarski('#skF_6'(A_2824)) = A_2824
      | ~ v1_zfmisc_1(A_2824)
      | v1_xboole_0(A_2824)
      | ~ v1_zfmisc_1(A_2824)
      | v1_xboole_0(A_2824) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2308])).

tff(c_28,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_17505,plain,(
    ! [C_3225,A_3226] :
      ( C_3225 = '#skF_6'(A_3226)
      | ~ r2_hidden(C_3225,A_3226)
      | ~ v1_zfmisc_1(A_3226)
      | v1_xboole_0(A_3226)
      | ~ v1_zfmisc_1(A_3226)
      | v1_xboole_0(A_3226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4593,c_28])).

tff(c_17877,plain,(
    ! [A_3240,B_3241] :
      ( '#skF_2'(A_3240,B_3241) = '#skF_6'(A_3240)
      | ~ v1_zfmisc_1(A_3240)
      | v1_xboole_0(A_3240)
      | r1_tarski(A_3240,B_3241) ) ),
    inference(resolution,[status(thm)],[c_10,c_17505])).

tff(c_18115,plain,
    ( '#skF_2'('#skF_7','#skF_8') = '#skF_6'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_17877,c_54])).

tff(c_18275,plain,
    ( '#skF_2'('#skF_7','#skF_8') = '#skF_6'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18115])).

tff(c_18276,plain,(
    '#skF_2'('#skF_7','#skF_8') = '#skF_6'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_18275])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18309,plain,
    ( ~ r2_hidden('#skF_6'('#skF_7'),'#skF_8')
    | r1_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_18276,c_8])).

tff(c_18328,plain,(
    ~ r2_hidden('#skF_6'('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_18309])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18958,plain,(
    ! [A_3262,B_3263] :
      ( '#skF_3'(A_3262,B_3263) = '#skF_6'(B_3263)
      | ~ v1_zfmisc_1(B_3263)
      | v1_xboole_0(B_3263)
      | r1_xboole_0(A_3262,B_3263) ) ),
    inference(resolution,[status(thm)],[c_14,c_17505])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59568,plain,(
    ! [A_54200,B_54201] :
      ( k4_xboole_0(A_54200,B_54201) = A_54200
      | '#skF_3'(A_54200,B_54201) = '#skF_6'(B_54201)
      | ~ v1_zfmisc_1(B_54201)
      | v1_xboole_0(B_54201) ) ),
    inference(resolution,[status(thm)],[c_18958,c_24])).

tff(c_59604,plain,(
    ! [A_54200] :
      ( k4_xboole_0(A_54200,'#skF_7') = A_54200
      | '#skF_3'(A_54200,'#skF_7') = '#skF_6'('#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_59568])).

tff(c_59609,plain,(
    ! [A_54310] :
      ( k4_xboole_0(A_54310,'#skF_7') = A_54310
      | '#skF_3'(A_54310,'#skF_7') = '#skF_6'('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_59604])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3898,plain,(
    ! [A_2788,B_2789,A_2790] :
      ( ~ r2_hidden('#skF_3'(A_2788,B_2789),A_2790)
      | k4_xboole_0(A_2790,A_2788) != A_2790
      | r1_xboole_0(A_2788,B_2789) ) ),
    inference(resolution,[status(thm)],[c_16,c_502])).

tff(c_3939,plain,(
    ! [B_2791,A_2792] :
      ( k4_xboole_0(B_2791,A_2792) != B_2791
      | r1_xboole_0(A_2792,B_2791) ) ),
    inference(resolution,[status(thm)],[c_14,c_3898])).

tff(c_3946,plain,(
    ! [A_2792,B_2791] :
      ( k4_xboole_0(A_2792,B_2791) = A_2792
      | k4_xboole_0(B_2791,A_2792) != B_2791 ) ),
    inference(resolution,[status(thm)],[c_3939,c_24])).

tff(c_60441,plain,(
    ! [A_54528] :
      ( k4_xboole_0('#skF_7',A_54528) = '#skF_7'
      | '#skF_3'(A_54528,'#skF_7') = '#skF_6'('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59609,c_3946])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60772,plain,(
    ! [A_54528] :
      ( k4_xboole_0('#skF_7','#skF_7') = k3_xboole_0('#skF_7',A_54528)
      | '#skF_3'(A_54528,'#skF_7') = '#skF_6'('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60441,c_22])).

tff(c_61548,plain,(
    ! [A_54967] :
      ( k3_xboole_0('#skF_7',A_54967) = k1_xboole_0
      | '#skF_3'(A_54967,'#skF_7') = '#skF_6'('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_60772])).

tff(c_62281,plain,(
    '#skF_3'('#skF_8','#skF_7') = '#skF_6'('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_61548,c_664])).

tff(c_62388,plain,
    ( r2_hidden('#skF_6'('#skF_7'),'#skF_8')
    | r1_xboole_0('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_62281,c_16])).

tff(c_62439,plain,(
    r1_xboole_0('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_18328,c_62388])).

tff(c_62663,plain,(
    k4_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_62439,c_24])).

tff(c_62885,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_62663,c_3946])).

tff(c_63116,plain,(
    k4_xboole_0('#skF_7','#skF_7') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_62885,c_22])).

tff(c_63210,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_63116])).

tff(c_63212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_63210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:32:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.24/9.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.24/9.13  
% 17.24/9.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.24/9.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5 > #skF_6 > #skF_4
% 17.24/9.13  
% 17.24/9.13  %Foreground sorts:
% 17.24/9.13  
% 17.24/9.13  
% 17.24/9.13  %Background operators:
% 17.24/9.13  
% 17.24/9.13  
% 17.24/9.13  %Foreground operators:
% 17.24/9.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.24/9.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.24/9.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.24/9.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.24/9.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.24/9.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.24/9.13  tff('#skF_7', type, '#skF_7': $i).
% 17.24/9.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.24/9.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 17.24/9.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.24/9.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.24/9.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.24/9.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.24/9.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.24/9.13  tff('#skF_8', type, '#skF_8': $i).
% 17.24/9.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.24/9.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.24/9.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.24/9.13  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 17.24/9.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.24/9.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.24/9.13  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 17.24/9.13  tff('#skF_6', type, '#skF_6': $i > $i).
% 17.24/9.13  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.24/9.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.24/9.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.24/9.13  
% 17.24/9.15  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 17.24/9.15  tff(f_60, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 17.24/9.15  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.24/9.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.24/9.15  tff(f_66, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 17.24/9.15  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 17.24/9.15  tff(f_108, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 17.24/9.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.24/9.15  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 17.24/9.15  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 17.24/9.15  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 17.24/9.15  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.24/9.15  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.24/9.15  tff(c_157, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.24/9.15  tff(c_172, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_157])).
% 17.24/9.15  tff(c_175, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_172])).
% 17.24/9.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.24/9.15  tff(c_26, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.24/9.15  tff(c_291, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, B_89) | ~r2_hidden(C_90, A_88))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.24/9.15  tff(c_502, plain, (![C_124, B_125, A_126]: (~r2_hidden(C_124, B_125) | ~r2_hidden(C_124, A_126) | k4_xboole_0(A_126, B_125)!=A_126)), inference(resolution, [status(thm)], [c_26, c_291])).
% 17.24/9.15  tff(c_624, plain, (![A_139, A_140]: (~r2_hidden('#skF_1'(A_139), A_140) | k4_xboole_0(A_140, A_139)!=A_140 | v1_xboole_0(A_139))), inference(resolution, [status(thm)], [c_4, c_502])).
% 17.24/9.15  tff(c_633, plain, (![A_1]: (k4_xboole_0(A_1, A_1)!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_624])).
% 17.24/9.15  tff(c_644, plain, (![A_141]: (k1_xboole_0!=A_141 | v1_xboole_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_633])).
% 17.24/9.15  tff(c_56, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.24/9.15  tff(c_664, plain, (k3_xboole_0('#skF_7', '#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_644, c_56])).
% 17.24/9.15  tff(c_54, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.24/9.15  tff(c_60, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.24/9.15  tff(c_58, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.24/9.15  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.24/9.15  tff(c_50, plain, (![A_35]: (k6_domain_1(A_35, '#skF_6'(A_35))=A_35 | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 17.24/9.15  tff(c_52, plain, (![A_35]: (m1_subset_1('#skF_6'(A_35), A_35) | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 17.24/9.15  tff(c_310, plain, (![A_94, B_95]: (k6_domain_1(A_94, B_95)=k1_tarski(B_95) | ~m1_subset_1(B_95, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.24/9.15  tff(c_2308, plain, (![A_2534]: (k6_domain_1(A_2534, '#skF_6'(A_2534))=k1_tarski('#skF_6'(A_2534)) | ~v1_zfmisc_1(A_2534) | v1_xboole_0(A_2534))), inference(resolution, [status(thm)], [c_52, c_310])).
% 17.24/9.15  tff(c_4593, plain, (![A_2824]: (k1_tarski('#skF_6'(A_2824))=A_2824 | ~v1_zfmisc_1(A_2824) | v1_xboole_0(A_2824) | ~v1_zfmisc_1(A_2824) | v1_xboole_0(A_2824))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2308])).
% 17.24/9.15  tff(c_28, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.24/9.15  tff(c_17505, plain, (![C_3225, A_3226]: (C_3225='#skF_6'(A_3226) | ~r2_hidden(C_3225, A_3226) | ~v1_zfmisc_1(A_3226) | v1_xboole_0(A_3226) | ~v1_zfmisc_1(A_3226) | v1_xboole_0(A_3226))), inference(superposition, [status(thm), theory('equality')], [c_4593, c_28])).
% 17.24/9.15  tff(c_17877, plain, (![A_3240, B_3241]: ('#skF_2'(A_3240, B_3241)='#skF_6'(A_3240) | ~v1_zfmisc_1(A_3240) | v1_xboole_0(A_3240) | r1_tarski(A_3240, B_3241))), inference(resolution, [status(thm)], [c_10, c_17505])).
% 17.24/9.15  tff(c_18115, plain, ('#skF_2'('#skF_7', '#skF_8')='#skF_6'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_17877, c_54])).
% 17.24/9.15  tff(c_18275, plain, ('#skF_2'('#skF_7', '#skF_8')='#skF_6'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18115])).
% 17.24/9.15  tff(c_18276, plain, ('#skF_2'('#skF_7', '#skF_8')='#skF_6'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_18275])).
% 17.24/9.15  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.24/9.15  tff(c_18309, plain, (~r2_hidden('#skF_6'('#skF_7'), '#skF_8') | r1_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_18276, c_8])).
% 17.24/9.15  tff(c_18328, plain, (~r2_hidden('#skF_6'('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_18309])).
% 17.24/9.15  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.24/9.15  tff(c_18958, plain, (![A_3262, B_3263]: ('#skF_3'(A_3262, B_3263)='#skF_6'(B_3263) | ~v1_zfmisc_1(B_3263) | v1_xboole_0(B_3263) | r1_xboole_0(A_3262, B_3263))), inference(resolution, [status(thm)], [c_14, c_17505])).
% 17.24/9.15  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.24/9.15  tff(c_59568, plain, (![A_54200, B_54201]: (k4_xboole_0(A_54200, B_54201)=A_54200 | '#skF_3'(A_54200, B_54201)='#skF_6'(B_54201) | ~v1_zfmisc_1(B_54201) | v1_xboole_0(B_54201))), inference(resolution, [status(thm)], [c_18958, c_24])).
% 17.24/9.15  tff(c_59604, plain, (![A_54200]: (k4_xboole_0(A_54200, '#skF_7')=A_54200 | '#skF_3'(A_54200, '#skF_7')='#skF_6'('#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_58, c_59568])).
% 17.24/9.15  tff(c_59609, plain, (![A_54310]: (k4_xboole_0(A_54310, '#skF_7')=A_54310 | '#skF_3'(A_54310, '#skF_7')='#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_60, c_59604])).
% 17.24/9.15  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.24/9.15  tff(c_3898, plain, (![A_2788, B_2789, A_2790]: (~r2_hidden('#skF_3'(A_2788, B_2789), A_2790) | k4_xboole_0(A_2790, A_2788)!=A_2790 | r1_xboole_0(A_2788, B_2789))), inference(resolution, [status(thm)], [c_16, c_502])).
% 17.24/9.15  tff(c_3939, plain, (![B_2791, A_2792]: (k4_xboole_0(B_2791, A_2792)!=B_2791 | r1_xboole_0(A_2792, B_2791))), inference(resolution, [status(thm)], [c_14, c_3898])).
% 17.24/9.15  tff(c_3946, plain, (![A_2792, B_2791]: (k4_xboole_0(A_2792, B_2791)=A_2792 | k4_xboole_0(B_2791, A_2792)!=B_2791)), inference(resolution, [status(thm)], [c_3939, c_24])).
% 17.24/9.15  tff(c_60441, plain, (![A_54528]: (k4_xboole_0('#skF_7', A_54528)='#skF_7' | '#skF_3'(A_54528, '#skF_7')='#skF_6'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_59609, c_3946])).
% 17.24/9.15  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.24/9.15  tff(c_60772, plain, (![A_54528]: (k4_xboole_0('#skF_7', '#skF_7')=k3_xboole_0('#skF_7', A_54528) | '#skF_3'(A_54528, '#skF_7')='#skF_6'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_60441, c_22])).
% 17.24/9.15  tff(c_61548, plain, (![A_54967]: (k3_xboole_0('#skF_7', A_54967)=k1_xboole_0 | '#skF_3'(A_54967, '#skF_7')='#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_60772])).
% 17.24/9.15  tff(c_62281, plain, ('#skF_3'('#skF_8', '#skF_7')='#skF_6'('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_61548, c_664])).
% 17.24/9.15  tff(c_62388, plain, (r2_hidden('#skF_6'('#skF_7'), '#skF_8') | r1_xboole_0('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_62281, c_16])).
% 17.24/9.15  tff(c_62439, plain, (r1_xboole_0('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_18328, c_62388])).
% 17.24/9.15  tff(c_62663, plain, (k4_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_62439, c_24])).
% 17.24/9.15  tff(c_62885, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_62663, c_3946])).
% 17.24/9.15  tff(c_63116, plain, (k4_xboole_0('#skF_7', '#skF_7')=k3_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62885, c_22])).
% 17.24/9.15  tff(c_63210, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_63116])).
% 17.24/9.15  tff(c_63212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_664, c_63210])).
% 17.24/9.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.24/9.15  
% 17.24/9.15  Inference rules
% 17.24/9.15  ----------------------
% 17.24/9.15  #Ref     : 0
% 17.24/9.15  #Sup     : 13789
% 17.24/9.15  #Fact    : 2
% 17.24/9.15  #Define  : 0
% 17.24/9.15  #Split   : 3
% 17.24/9.15  #Chain   : 0
% 17.24/9.15  #Close   : 0
% 17.24/9.15  
% 17.24/9.15  Ordering : KBO
% 17.24/9.15  
% 17.24/9.15  Simplification rules
% 17.24/9.15  ----------------------
% 17.24/9.15  #Subsume      : 5552
% 17.24/9.15  #Demod        : 3686
% 17.24/9.15  #Tautology    : 2085
% 17.24/9.15  #SimpNegUnit  : 754
% 17.24/9.15  #BackRed      : 0
% 17.24/9.15  
% 17.24/9.15  #Partial instantiations: 34425
% 17.24/9.15  #Strategies tried      : 1
% 17.24/9.15  
% 17.24/9.15  Timing (in seconds)
% 17.24/9.15  ----------------------
% 17.24/9.15  Preprocessing        : 0.32
% 17.24/9.15  Parsing              : 0.16
% 17.24/9.15  CNF conversion       : 0.02
% 17.24/9.15  Main loop            : 8.07
% 17.24/9.15  Inferencing          : 1.99
% 17.24/9.15  Reduction            : 2.15
% 17.24/9.15  Demodulation         : 1.42
% 17.24/9.15  BG Simplification    : 0.20
% 17.24/9.15  Subsumption          : 3.37
% 17.24/9.15  Abstraction          : 0.34
% 17.24/9.15  MUC search           : 0.00
% 17.24/9.15  Cooper               : 0.00
% 17.24/9.15  Total                : 8.42
% 17.24/9.15  Index Insertion      : 0.00
% 17.24/9.15  Index Deletion       : 0.00
% 17.24/9.15  Index Matching       : 0.00
% 17.24/9.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
