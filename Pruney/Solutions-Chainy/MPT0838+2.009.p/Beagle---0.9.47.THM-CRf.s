%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:10 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 165 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 328 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_152,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_161,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_152])).

tff(c_162,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_32])).

tff(c_111,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_71,C_72,B_73] :
      ( m1_subset_1(A_71,C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_167,plain,(
    ! [A_83,B_84,A_85] :
      ( m1_subset_1(A_83,B_84)
      | ~ r2_hidden(A_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_173,plain,(
    ! [A_1,B_84] :
      ( m1_subset_1('#skF_1'(A_1),B_84)
      | ~ r1_tarski(A_1,B_84)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_209,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_223,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_56,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_61,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_224,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_110])).

tff(c_233,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_173,c_224])).

tff(c_253,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_256,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_120,c_256])).

tff(c_261,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_139,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),k2_relat_1(B_75))
      | ~ r2_hidden(A_74,k1_relat_1(B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [B_77,A_78] :
      ( ~ v1_xboole_0(k2_relat_1(B_77))
      | ~ r2_hidden(A_78,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_150,plain,(
    ! [B_77] :
      ( ~ v1_xboole_0(k2_relat_1(B_77))
      | ~ v1_relat_1(B_77)
      | v1_xboole_0(k1_relat_1(B_77)) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_265,plain,
    ( ~ v1_relat_1('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_261,c_150])).

tff(c_271,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_265])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_275,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_271,c_6])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_275])).

tff(c_280,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_285,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_6])).

tff(c_296,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_280])).

tff(c_378,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_389,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_378])).

tff(c_393,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_389])).

tff(c_338,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_2'(A_110,B_111),k2_relat_1(B_111))
      | ~ r2_hidden(A_110,k1_relat_1(B_111))
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_346,plain,(
    ! [B_112,A_113] :
      ( ~ v1_xboole_0(k2_relat_1(B_112))
      | ~ r2_hidden(A_113,k1_relat_1(B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_351,plain,(
    ! [B_112] :
      ( ~ v1_xboole_0(k2_relat_1(B_112))
      | ~ v1_relat_1(B_112)
      | v1_xboole_0(k1_relat_1(B_112)) ) ),
    inference(resolution,[status(thm)],[c_4,c_346])).

tff(c_397,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_351])).

tff(c_410,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_296,c_397])).

tff(c_421,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_410,c_6])).

tff(c_441,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_452,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_441])).

tff(c_456,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_452])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.35/1.30  
% 2.35/1.30  %Foreground sorts:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Background operators:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Foreground operators:
% 2.35/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.35/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.35/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.35/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.35/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.30  
% 2.35/1.32  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.35/1.32  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.35/1.32  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.32  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.35/1.32  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.35/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.35/1.32  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.35/1.32  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.35/1.32  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.35/1.32  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 2.35/1.32  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.35/1.32  tff(c_32, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.35/1.32  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.35/1.32  tff(c_62, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.35/1.32  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.35/1.32  tff(c_152, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.32  tff(c_161, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_152])).
% 2.35/1.32  tff(c_162, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_161, c_32])).
% 2.35/1.32  tff(c_111, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.32  tff(c_120, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_111])).
% 2.35/1.32  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.35/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.32  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.32  tff(c_132, plain, (![A_71, C_72, B_73]: (m1_subset_1(A_71, C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.32  tff(c_167, plain, (![A_83, B_84, A_85]: (m1_subset_1(A_83, B_84) | ~r2_hidden(A_83, A_85) | ~r1_tarski(A_85, B_84))), inference(resolution, [status(thm)], [c_10, c_132])).
% 2.35/1.32  tff(c_173, plain, (![A_1, B_84]: (m1_subset_1('#skF_1'(A_1), B_84) | ~r1_tarski(A_1, B_84) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_167])).
% 2.35/1.32  tff(c_209, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.35/1.32  tff(c_223, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_209])).
% 2.35/1.32  tff(c_56, plain, (![D_48]: (~r2_hidden(D_48, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.35/1.32  tff(c_61, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.35/1.32  tff(c_110, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_61])).
% 2.35/1.32  tff(c_224, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_110])).
% 2.35/1.32  tff(c_233, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_173, c_224])).
% 2.35/1.32  tff(c_253, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_233])).
% 2.35/1.32  tff(c_256, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_253])).
% 2.35/1.32  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_120, c_256])).
% 2.35/1.32  tff(c_261, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_233])).
% 2.35/1.32  tff(c_139, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), k2_relat_1(B_75)) | ~r2_hidden(A_74, k1_relat_1(B_75)) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.32  tff(c_145, plain, (![B_77, A_78]: (~v1_xboole_0(k2_relat_1(B_77)) | ~r2_hidden(A_78, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_139, c_2])).
% 2.35/1.32  tff(c_150, plain, (![B_77]: (~v1_xboole_0(k2_relat_1(B_77)) | ~v1_relat_1(B_77) | v1_xboole_0(k1_relat_1(B_77)))), inference(resolution, [status(thm)], [c_4, c_145])).
% 2.35/1.32  tff(c_265, plain, (~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_261, c_150])).
% 2.35/1.32  tff(c_271, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_265])).
% 2.35/1.32  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.32  tff(c_275, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_271, c_6])).
% 2.35/1.32  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_275])).
% 2.35/1.32  tff(c_280, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_61])).
% 2.35/1.32  tff(c_285, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_6])).
% 2.35/1.32  tff(c_296, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_285, c_280])).
% 2.35/1.32  tff(c_378, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.35/1.32  tff(c_389, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_378])).
% 2.35/1.32  tff(c_393, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_285, c_389])).
% 2.35/1.32  tff(c_338, plain, (![A_110, B_111]: (r2_hidden('#skF_2'(A_110, B_111), k2_relat_1(B_111)) | ~r2_hidden(A_110, k1_relat_1(B_111)) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.32  tff(c_346, plain, (![B_112, A_113]: (~v1_xboole_0(k2_relat_1(B_112)) | ~r2_hidden(A_113, k1_relat_1(B_112)) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_338, c_2])).
% 2.35/1.32  tff(c_351, plain, (![B_112]: (~v1_xboole_0(k2_relat_1(B_112)) | ~v1_relat_1(B_112) | v1_xboole_0(k1_relat_1(B_112)))), inference(resolution, [status(thm)], [c_4, c_346])).
% 2.35/1.32  tff(c_397, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_393, c_351])).
% 2.35/1.32  tff(c_410, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_296, c_397])).
% 2.35/1.32  tff(c_421, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_410, c_6])).
% 2.35/1.32  tff(c_441, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.35/1.32  tff(c_452, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_441])).
% 2.35/1.32  tff(c_456, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_421, c_452])).
% 2.35/1.32  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_456])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.32  #Sup     : 84
% 2.35/1.32  #Fact    : 0
% 2.35/1.32  #Define  : 0
% 2.35/1.32  #Split   : 2
% 2.35/1.32  #Chain   : 0
% 2.35/1.32  #Close   : 0
% 2.35/1.32  
% 2.35/1.32  Ordering : KBO
% 2.35/1.32  
% 2.35/1.32  Simplification rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Subsume      : 2
% 2.35/1.32  #Demod        : 28
% 2.35/1.32  #Tautology    : 21
% 2.35/1.32  #SimpNegUnit  : 2
% 2.35/1.32  #BackRed      : 6
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.32  Preprocessing        : 0.31
% 2.35/1.32  Parsing              : 0.16
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.26
% 2.35/1.32  Inferencing          : 0.11
% 2.35/1.32  Reduction            : 0.07
% 2.35/1.32  Demodulation         : 0.05
% 2.35/1.32  BG Simplification    : 0.01
% 2.35/1.32  Subsumption          : 0.04
% 2.35/1.32  Abstraction          : 0.02
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.60
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
