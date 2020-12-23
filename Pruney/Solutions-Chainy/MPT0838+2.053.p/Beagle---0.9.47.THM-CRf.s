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
% DateTime   : Thu Dec  3 10:08:16 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 248 expanded)
%              Number of leaves         :   37 (  97 expanded)
%              Depth                    :    8
%              Number of atoms          :  130 ( 517 expanded)
%              Number of equality atoms :   47 ( 143 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_20,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_165,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_171,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_165])).

tff(c_175,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_171])).

tff(c_22,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_182,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_175,c_22])).

tff(c_191,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_220,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_229,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_220])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_337,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_351,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_337])).

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

tff(c_257,plain,(
    ! [A_87,C_88,B_89] :
      ( m1_subset_1(A_87,C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_276,plain,(
    ! [A_94,B_95,A_96] :
      ( m1_subset_1(A_94,B_95)
      | ~ r2_hidden(A_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_10,c_257])).

tff(c_303,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1('#skF_1'(A_106),B_107)
      | ~ r1_tarski(A_106,B_107)
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_4,c_276])).

tff(c_185,plain,(
    ! [D_68] :
      ( ~ r2_hidden(D_68,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_68,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_190,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_185])).

tff(c_230,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_333,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_303,c_230])).

tff(c_368,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_351,c_333])).

tff(c_369,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_372,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_369])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_229,c_372])).

tff(c_377,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_381,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_377,c_6])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_381])).

tff(c_386,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_391,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_386,c_6])).

tff(c_492,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_503,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_492])).

tff(c_507,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_503])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_507])).

tff(c_510,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_28,plain,(
    ! [A_19] : k1_relat_1('#skF_2'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_19] : v1_relat_1('#skF_2'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) != k1_xboole_0
      | k1_xboole_0 = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_77,plain,(
    ! [A_19] :
      ( k1_relat_1('#skF_2'(A_19)) != k1_xboole_0
      | '#skF_2'(A_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_82,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | '#skF_2'(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_77])).

tff(c_88,plain,(
    ! [A_58] :
      ( k1_relat_1(k1_xboole_0) = A_58
      | k1_xboole_0 != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_28])).

tff(c_542,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_510,c_88])).

tff(c_24,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_183,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_175,c_24])).

tff(c_184,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_512,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_184])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_512])).

tff(c_546,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_44,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_554,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_44])).

tff(c_547,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_567,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_547])).

tff(c_879,plain,(
    ! [A_198,B_199,C_200] :
      ( k1_relset_1(A_198,B_199,C_200) = k1_relat_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_890,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_879])).

tff(c_894,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_890])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_554,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  
% 3.01/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.49  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.01/1.49  
% 3.01/1.49  %Foreground sorts:
% 3.01/1.49  
% 3.01/1.49  
% 3.01/1.49  %Background operators:
% 3.01/1.49  
% 3.01/1.49  
% 3.01/1.49  %Foreground operators:
% 3.01/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.01/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.01/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.01/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.01/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.01/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.49  
% 3.01/1.51  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.01/1.51  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.01/1.51  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.01/1.51  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.01/1.51  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.01/1.51  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.01/1.51  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.01/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.01/1.51  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.01/1.51  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.01/1.51  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.01/1.51  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 3.01/1.51  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.01/1.51  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.01/1.51  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.51  tff(c_165, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.01/1.51  tff(c_171, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_165])).
% 3.01/1.51  tff(c_175, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_171])).
% 3.01/1.51  tff(c_22, plain, (![A_18]: (k2_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.51  tff(c_182, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_175, c_22])).
% 3.01/1.51  tff(c_191, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_182])).
% 3.01/1.51  tff(c_220, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.01/1.51  tff(c_229, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_220])).
% 3.01/1.51  tff(c_18, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.01/1.51  tff(c_337, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.01/1.51  tff(c_351, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_337])).
% 3.01/1.51  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.51  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.51  tff(c_257, plain, (![A_87, C_88, B_89]: (m1_subset_1(A_87, C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.01/1.51  tff(c_276, plain, (![A_94, B_95, A_96]: (m1_subset_1(A_94, B_95) | ~r2_hidden(A_94, A_96) | ~r1_tarski(A_96, B_95))), inference(resolution, [status(thm)], [c_10, c_257])).
% 3.01/1.51  tff(c_303, plain, (![A_106, B_107]: (m1_subset_1('#skF_1'(A_106), B_107) | ~r1_tarski(A_106, B_107) | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_4, c_276])).
% 3.01/1.51  tff(c_185, plain, (![D_68]: (~r2_hidden(D_68, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_68, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.51  tff(c_190, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_185])).
% 3.01/1.51  tff(c_230, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_190])).
% 3.01/1.51  tff(c_333, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_303, c_230])).
% 3.01/1.51  tff(c_368, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_351, c_333])).
% 3.01/1.51  tff(c_369, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_368])).
% 3.01/1.51  tff(c_372, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_369])).
% 3.01/1.51  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_229, c_372])).
% 3.01/1.51  tff(c_377, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_368])).
% 3.01/1.51  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.51  tff(c_381, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_377, c_6])).
% 3.01/1.51  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_381])).
% 3.01/1.51  tff(c_386, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_190])).
% 3.01/1.51  tff(c_391, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_386, c_6])).
% 3.01/1.51  tff(c_492, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.01/1.51  tff(c_503, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_492])).
% 3.01/1.51  tff(c_507, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_391, c_503])).
% 3.01/1.51  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_507])).
% 3.01/1.51  tff(c_510, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_182])).
% 3.01/1.51  tff(c_28, plain, (![A_19]: (k1_relat_1('#skF_2'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.51  tff(c_32, plain, (![A_19]: (v1_relat_1('#skF_2'(A_19)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.51  tff(c_71, plain, (![A_57]: (k1_relat_1(A_57)!=k1_xboole_0 | k1_xboole_0=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.51  tff(c_77, plain, (![A_19]: (k1_relat_1('#skF_2'(A_19))!=k1_xboole_0 | '#skF_2'(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_71])).
% 3.01/1.51  tff(c_82, plain, (![A_58]: (k1_xboole_0!=A_58 | '#skF_2'(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_77])).
% 3.01/1.51  tff(c_88, plain, (![A_58]: (k1_relat_1(k1_xboole_0)=A_58 | k1_xboole_0!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_82, c_28])).
% 3.01/1.51  tff(c_542, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_510, c_88])).
% 3.01/1.51  tff(c_24, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.51  tff(c_183, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_175, c_24])).
% 3.01/1.51  tff(c_184, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_183])).
% 3.01/1.51  tff(c_512, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_184])).
% 3.01/1.51  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_542, c_512])).
% 3.01/1.51  tff(c_546, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_183])).
% 3.01/1.51  tff(c_44, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.01/1.51  tff(c_554, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_44])).
% 3.01/1.51  tff(c_547, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_183])).
% 3.01/1.51  tff(c_567, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_547])).
% 3.01/1.51  tff(c_879, plain, (![A_198, B_199, C_200]: (k1_relset_1(A_198, B_199, C_200)=k1_relat_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.51  tff(c_890, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_879])).
% 3.01/1.51  tff(c_894, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_567, c_890])).
% 3.01/1.51  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_554, c_894])).
% 3.01/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.51  
% 3.01/1.51  Inference rules
% 3.01/1.51  ----------------------
% 3.01/1.51  #Ref     : 3
% 3.01/1.51  #Sup     : 162
% 3.01/1.51  #Fact    : 0
% 3.01/1.51  #Define  : 0
% 3.01/1.51  #Split   : 9
% 3.01/1.51  #Chain   : 0
% 3.01/1.51  #Close   : 0
% 3.01/1.51  
% 3.01/1.51  Ordering : KBO
% 3.01/1.51  
% 3.01/1.51  Simplification rules
% 3.01/1.51  ----------------------
% 3.01/1.51  #Subsume      : 15
% 3.01/1.51  #Demod        : 89
% 3.01/1.51  #Tautology    : 67
% 3.01/1.51  #SimpNegUnit  : 9
% 3.01/1.51  #BackRed      : 31
% 3.01/1.51  
% 3.01/1.51  #Partial instantiations: 0
% 3.01/1.51  #Strategies tried      : 1
% 3.01/1.51  
% 3.01/1.51  Timing (in seconds)
% 3.01/1.51  ----------------------
% 3.01/1.51  Preprocessing        : 0.31
% 3.01/1.51  Parsing              : 0.17
% 3.01/1.51  CNF conversion       : 0.02
% 3.01/1.51  Main loop            : 0.38
% 3.01/1.51  Inferencing          : 0.16
% 3.01/1.51  Reduction            : 0.11
% 3.01/1.51  Demodulation         : 0.07
% 3.01/1.51  BG Simplification    : 0.02
% 3.01/1.51  Subsumption          : 0.05
% 3.01/1.51  Abstraction          : 0.02
% 3.01/1.51  MUC search           : 0.00
% 3.01/1.51  Cooper               : 0.00
% 3.01/1.51  Total                : 0.73
% 3.01/1.51  Index Insertion      : 0.00
% 3.01/1.51  Index Deletion       : 0.00
% 3.01/1.51  Index Matching       : 0.00
% 3.01/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
