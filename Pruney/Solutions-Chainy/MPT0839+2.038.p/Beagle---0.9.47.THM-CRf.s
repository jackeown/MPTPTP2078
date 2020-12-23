%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:26 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 142 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 284 expanded)
%              Number of equality atoms :   26 (  55 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_115,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_121])).

tff(c_30,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) = k1_xboole_0
      | k2_relat_1(A_21) != k1_xboole_0
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_30])).

tff(c_135,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_32,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) = k1_xboole_0
      | k1_relat_1(A_21) != k1_xboole_0
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_133,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_32])).

tff(c_136,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_133])).

tff(c_381,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_390,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_381])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_391,plain,(
    ! [A_116,C_117,B_118] :
      ( m1_subset_1(A_116,C_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(C_117))
      | ~ r2_hidden(A_116,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_459,plain,(
    ! [A_128,B_129,A_130] :
      ( m1_subset_1(A_128,B_129)
      | ~ r2_hidden(A_128,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(resolution,[status(thm)],[c_18,c_391])).

tff(c_679,plain,(
    ! [A_170,B_171,B_172] :
      ( m1_subset_1('#skF_1'(A_170,B_171),B_172)
      | ~ r1_tarski(A_170,B_172)
      | r1_tarski(A_170,B_171) ) ),
    inference(resolution,[status(thm)],[c_6,c_459])).

tff(c_517,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_526,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_517])).

tff(c_92,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_97,plain,(
    ! [B_56] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_56),'#skF_3')
      | r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_56) ) ),
    inference(resolution,[status(thm)],[c_92,c_42])).

tff(c_527,plain,(
    ! [B_56] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4'),B_56),'#skF_3')
      | r1_tarski(k1_relat_1('#skF_4'),B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_526,c_97])).

tff(c_711,plain,(
    ! [B_171] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
      | r1_tarski(k1_relat_1('#skF_4'),B_171) ) ),
    inference(resolution,[status(thm)],[c_679,c_527])).

tff(c_746,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_749,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_746])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_390,c_749])).

tff(c_757,plain,(
    ! [B_175] : r1_tarski(k1_relat_1('#skF_4'),B_175) ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_787,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_757,c_78])).

tff(c_802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_787])).

tff(c_804,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_1184,plain,(
    ! [A_239,B_240,C_241] :
      ( k2_relset_1(A_239,B_240,C_241) = k2_relat_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1191,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1184])).

tff(c_1194,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_1191])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.71  
% 3.44/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.71  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.44/1.71  
% 3.44/1.71  %Foreground sorts:
% 3.44/1.71  
% 3.44/1.71  
% 3.44/1.71  %Background operators:
% 3.44/1.71  
% 3.44/1.71  
% 3.44/1.71  %Foreground operators:
% 3.44/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.44/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.71  
% 3.44/1.73  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.44/1.73  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.44/1.73  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.44/1.73  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.44/1.73  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.44/1.73  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.44/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.44/1.73  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.73  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.44/1.73  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.44/1.73  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.44/1.73  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.73  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.44/1.73  tff(c_44, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.44/1.73  tff(c_28, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.44/1.73  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.44/1.73  tff(c_115, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.73  tff(c_121, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_115])).
% 3.44/1.73  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_121])).
% 3.44/1.73  tff(c_30, plain, (![A_21]: (k1_relat_1(A_21)=k1_xboole_0 | k2_relat_1(A_21)!=k1_xboole_0 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.73  tff(c_132, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_30])).
% 3.44/1.73  tff(c_135, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_132])).
% 3.44/1.73  tff(c_32, plain, (![A_21]: (k2_relat_1(A_21)=k1_xboole_0 | k1_relat_1(A_21)!=k1_xboole_0 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.73  tff(c_133, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_32])).
% 3.44/1.73  tff(c_136, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_135, c_133])).
% 3.44/1.73  tff(c_381, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.73  tff(c_390, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_381])).
% 3.44/1.73  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.73  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.73  tff(c_391, plain, (![A_116, C_117, B_118]: (m1_subset_1(A_116, C_117) | ~m1_subset_1(B_118, k1_zfmisc_1(C_117)) | ~r2_hidden(A_116, B_118))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.73  tff(c_459, plain, (![A_128, B_129, A_130]: (m1_subset_1(A_128, B_129) | ~r2_hidden(A_128, A_130) | ~r1_tarski(A_130, B_129))), inference(resolution, [status(thm)], [c_18, c_391])).
% 3.44/1.73  tff(c_679, plain, (![A_170, B_171, B_172]: (m1_subset_1('#skF_1'(A_170, B_171), B_172) | ~r1_tarski(A_170, B_172) | r1_tarski(A_170, B_171))), inference(resolution, [status(thm)], [c_6, c_459])).
% 3.44/1.73  tff(c_517, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.73  tff(c_526, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_517])).
% 3.44/1.73  tff(c_92, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.73  tff(c_42, plain, (![D_42]: (~r2_hidden(D_42, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.44/1.73  tff(c_97, plain, (![B_56]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_56), '#skF_3') | r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_56))), inference(resolution, [status(thm)], [c_92, c_42])).
% 3.44/1.73  tff(c_527, plain, (![B_56]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4'), B_56), '#skF_3') | r1_tarski(k1_relat_1('#skF_4'), B_56))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_526, c_97])).
% 3.44/1.73  tff(c_711, plain, (![B_171]: (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | r1_tarski(k1_relat_1('#skF_4'), B_171))), inference(resolution, [status(thm)], [c_679, c_527])).
% 3.44/1.73  tff(c_746, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_711])).
% 3.44/1.73  tff(c_749, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_746])).
% 3.44/1.73  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_390, c_749])).
% 3.44/1.73  tff(c_757, plain, (![B_175]: (r1_tarski(k1_relat_1('#skF_4'), B_175))), inference(splitRight, [status(thm)], [c_711])).
% 3.44/1.73  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.73  tff(c_66, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.73  tff(c_78, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_66])).
% 3.44/1.73  tff(c_787, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_757, c_78])).
% 3.44/1.73  tff(c_802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_787])).
% 3.44/1.73  tff(c_804, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 3.44/1.73  tff(c_1184, plain, (![A_239, B_240, C_241]: (k2_relset_1(A_239, B_240, C_241)=k2_relat_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.44/1.73  tff(c_1191, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1184])).
% 3.44/1.73  tff(c_1194, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_804, c_1191])).
% 3.44/1.73  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1194])).
% 3.44/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.73  
% 3.44/1.73  Inference rules
% 3.44/1.73  ----------------------
% 3.44/1.73  #Ref     : 0
% 3.44/1.73  #Sup     : 221
% 3.44/1.73  #Fact    : 0
% 3.44/1.73  #Define  : 0
% 3.44/1.73  #Split   : 10
% 3.44/1.73  #Chain   : 0
% 3.44/1.73  #Close   : 0
% 3.44/1.73  
% 3.44/1.73  Ordering : KBO
% 3.44/1.73  
% 3.44/1.73  Simplification rules
% 3.44/1.73  ----------------------
% 3.44/1.73  #Subsume      : 13
% 3.44/1.73  #Demod        : 122
% 3.44/1.73  #Tautology    : 92
% 3.44/1.73  #SimpNegUnit  : 15
% 3.44/1.73  #BackRed      : 9
% 3.44/1.73  
% 3.44/1.73  #Partial instantiations: 0
% 3.44/1.73  #Strategies tried      : 1
% 3.44/1.73  
% 3.44/1.73  Timing (in seconds)
% 3.44/1.73  ----------------------
% 3.44/1.73  Preprocessing        : 0.44
% 3.44/1.73  Parsing              : 0.24
% 3.44/1.73  CNF conversion       : 0.03
% 3.44/1.73  Main loop            : 0.51
% 3.44/1.73  Inferencing          : 0.20
% 3.44/1.73  Reduction            : 0.16
% 3.44/1.73  Demodulation         : 0.11
% 3.44/1.73  BG Simplification    : 0.02
% 3.44/1.73  Subsumption          : 0.09
% 3.44/1.73  Abstraction          : 0.03
% 3.44/1.73  MUC search           : 0.00
% 3.44/1.73  Cooper               : 0.00
% 3.44/1.73  Total                : 1.00
% 3.44/1.73  Index Insertion      : 0.00
% 3.44/1.73  Index Deletion       : 0.00
% 3.44/1.73  Index Matching       : 0.00
% 3.44/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
