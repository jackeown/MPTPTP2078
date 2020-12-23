%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 182 expanded)
%              Number of leaves         :   39 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 536 expanded)
%              Number of equality atoms :   35 (  83 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_211,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_224,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_211])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_238,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_48])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_104])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_182,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_195,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_182])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_510,plain,(
    ! [E_121,A_122,F_120,D_125,B_124,C_123] :
      ( k1_partfun1(A_122,B_124,C_123,D_125,E_121,F_120) = k5_relat_1(E_121,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_123,D_125)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_124)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_520,plain,(
    ! [A_122,B_124,E_121] :
      ( k1_partfun1(A_122,B_124,'#skF_1','#skF_2',E_121,'#skF_3') = k5_relat_1(E_121,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_124)))
      | ~ v1_funct_1(E_121) ) ),
    inference(resolution,[status(thm)],[c_58,c_510])).

tff(c_555,plain,(
    ! [A_129,B_130,E_131] :
      ( k1_partfun1(A_129,B_130,'#skF_1','#skF_2',E_131,'#skF_3') = k5_relat_1(E_131,'#skF_3')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_520])).

tff(c_567,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_555])).

tff(c_576,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_567])).

tff(c_596,plain,(
    ! [F_135,A_132,D_133,B_136,E_137,C_134] :
      ( m1_subset_1(k1_partfun1(A_132,B_136,C_134,D_133,E_137,F_135),k1_zfmisc_1(k2_zfmisc_1(A_132,D_133)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_134,D_133)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_132,B_136)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_629,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_596])).

tff(c_645,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_62,c_58,c_629])).

tff(c_36,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_331,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_339,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_331])).

tff(c_354,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_339])).

tff(c_911,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_576,c_576,c_354])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [B_36,A_35] :
      ( m1_subset_1(B_36,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_36),A_35)))
      | ~ r1_tarski(k2_relat_1(B_36),A_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1508,plain,(
    ! [B_194,A_190,B_191,E_193,A_192] :
      ( k1_partfun1(A_192,B_191,k1_relat_1(B_194),A_190,E_193,B_194) = k5_relat_1(E_193,B_194)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191)))
      | ~ v1_funct_1(E_193)
      | ~ r1_tarski(k2_relat_1(B_194),A_190)
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_42,c_510])).

tff(c_1526,plain,(
    ! [B_194,A_190] :
      ( k1_partfun1('#skF_2','#skF_1',k1_relat_1(B_194),A_190,'#skF_4',B_194) = k5_relat_1('#skF_4',B_194)
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1(B_194),A_190)
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_52,c_1508])).

tff(c_2237,plain,(
    ! [B_240,A_241] :
      ( k1_partfun1('#skF_2','#skF_1',k1_relat_1(B_240),A_241,'#skF_4',B_240) = k5_relat_1('#skF_4',B_240)
      | ~ r1_tarski(k2_relat_1(B_240),A_241)
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1526])).

tff(c_2248,plain,(
    ! [B_240] :
      ( k1_partfun1('#skF_2','#skF_1',k1_relat_1(B_240),k2_relat_1(B_240),'#skF_4',B_240) = k5_relat_1('#skF_4',B_240)
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240) ) ),
    inference(resolution,[status(thm)],[c_6,c_2237])).

tff(c_20,plain,(
    ! [C_13,B_12,A_11] :
      ( v5_relat_1(C_13,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1233,plain,(
    ! [D_177,F_178,B_175,C_174,E_176,A_173] :
      ( v5_relat_1(k1_partfun1(A_173,B_175,C_174,D_177,E_176,F_178),D_177)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(C_174,D_177)))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_173,B_175)))
      | ~ v1_funct_1(E_176) ) ),
    inference(resolution,[status(thm)],[c_596,c_20])).

tff(c_5746,plain,(
    ! [E_435,A_433,B_436,A_434,B_437] :
      ( v5_relat_1(k1_partfun1(A_434,B_437,k1_relat_1(B_436),A_433,E_435,B_436),A_433)
      | ~ m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(A_434,B_437)))
      | ~ v1_funct_1(E_435)
      | ~ r1_tarski(k2_relat_1(B_436),A_433)
      | ~ v1_funct_1(B_436)
      | ~ v1_relat_1(B_436) ) ),
    inference(resolution,[status(thm)],[c_42,c_1233])).

tff(c_5764,plain,(
    ! [B_240] :
      ( v5_relat_1(k5_relat_1('#skF_4',B_240),k2_relat_1(B_240))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1(B_240),k2_relat_1(B_240))
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240)
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2248,c_5746])).

tff(c_5829,plain,(
    ! [B_445] :
      ( v5_relat_1(k5_relat_1('#skF_4',B_445),k2_relat_1(B_445))
      | ~ v1_funct_1(B_445)
      | ~ v1_relat_1(B_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_52,c_5764])).

tff(c_5834,plain,
    ( v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_5829])).

tff(c_5840,plain,(
    v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_62,c_5834])).

tff(c_107,plain,(
    ! [A_27] :
      ( v1_relat_1(k6_partfun1(A_27))
      | ~ v1_relat_1(k2_zfmisc_1(A_27,A_27)) ) ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_116,plain,(
    ! [A_27] : v1_relat_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_107])).

tff(c_40,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(k2_relat_1(B_51),A_52)
      | ~ v5_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(B_76) = A_77
      | ~ r1_tarski(A_77,k2_relat_1(B_76))
      | ~ v5_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_2805,plain,(
    ! [B_255,B_254] :
      ( k2_relat_1(B_255) = k2_relat_1(B_254)
      | ~ v5_relat_1(B_254,k2_relat_1(B_255))
      | ~ v1_relat_1(B_254)
      | ~ v5_relat_1(B_255,k2_relat_1(B_254))
      | ~ v1_relat_1(B_255) ) ),
    inference(resolution,[status(thm)],[c_12,c_244])).

tff(c_2815,plain,(
    ! [A_10,B_254] :
      ( k2_relat_1(k6_partfun1(A_10)) = k2_relat_1(B_254)
      | ~ v5_relat_1(B_254,A_10)
      | ~ v1_relat_1(B_254)
      | ~ v5_relat_1(k6_partfun1(A_10),k2_relat_1(B_254))
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_2805])).

tff(c_2825,plain,(
    ! [B_254,A_10] :
      ( k2_relat_1(B_254) = A_10
      | ~ v5_relat_1(B_254,A_10)
      | ~ v1_relat_1(B_254)
      | ~ v5_relat_1(k6_partfun1(A_10),k2_relat_1(B_254)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_63,c_2815])).

tff(c_5847,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5840,c_2825])).

tff(c_5863,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_195,c_5847])).

tff(c_5865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_5863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.58/3.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.15  
% 8.58/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.16  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.58/3.16  
% 8.58/3.16  %Foreground sorts:
% 8.58/3.16  
% 8.58/3.16  
% 8.58/3.16  %Background operators:
% 8.58/3.16  
% 8.58/3.16  
% 8.58/3.16  %Foreground operators:
% 8.58/3.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.58/3.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.58/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.58/3.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.58/3.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.58/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.58/3.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.58/3.16  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.58/3.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.58/3.16  tff('#skF_2', type, '#skF_2': $i).
% 8.58/3.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.58/3.16  tff('#skF_3', type, '#skF_3': $i).
% 8.58/3.16  tff('#skF_1', type, '#skF_1': $i).
% 8.58/3.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.58/3.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.58/3.16  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.58/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.58/3.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.58/3.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.58/3.16  tff('#skF_4', type, '#skF_4': $i).
% 8.58/3.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.58/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.58/3.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.58/3.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.58/3.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.58/3.16  
% 8.58/3.17  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.58/3.17  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.58/3.17  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.58/3.17  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.58/3.17  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.58/3.17  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.58/3.17  tff(f_80, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.58/3.17  tff(f_84, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.58/3.17  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.58/3.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.58/3.17  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 8.58/3.17  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.58/3.17  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.58/3.17  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.58/3.17  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.17  tff(c_211, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.58/3.17  tff(c_224, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_211])).
% 8.58/3.17  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.17  tff(c_238, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_48])).
% 8.58/3.17  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.58/3.17  tff(c_104, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.58/3.17  tff(c_113, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_104])).
% 8.58/3.17  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_113])).
% 8.58/3.17  tff(c_182, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.58/3.17  tff(c_195, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_182])).
% 8.58/3.17  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.17  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.17  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.17  tff(c_510, plain, (![E_121, A_122, F_120, D_125, B_124, C_123]: (k1_partfun1(A_122, B_124, C_123, D_125, E_121, F_120)=k5_relat_1(E_121, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_123, D_125))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_124))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.58/3.17  tff(c_520, plain, (![A_122, B_124, E_121]: (k1_partfun1(A_122, B_124, '#skF_1', '#skF_2', E_121, '#skF_3')=k5_relat_1(E_121, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_124))) | ~v1_funct_1(E_121))), inference(resolution, [status(thm)], [c_58, c_510])).
% 8.58/3.17  tff(c_555, plain, (![A_129, B_130, E_131]: (k1_partfun1(A_129, B_130, '#skF_1', '#skF_2', E_131, '#skF_3')=k5_relat_1(E_131, '#skF_3') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_131))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_520])).
% 8.58/3.17  tff(c_567, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_555])).
% 8.58/3.17  tff(c_576, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_567])).
% 8.58/3.17  tff(c_596, plain, (![F_135, A_132, D_133, B_136, E_137, C_134]: (m1_subset_1(k1_partfun1(A_132, B_136, C_134, D_133, E_137, F_135), k1_zfmisc_1(k2_zfmisc_1(A_132, D_133))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_134, D_133))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_132, B_136))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.58/3.17  tff(c_629, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_576, c_596])).
% 8.58/3.17  tff(c_645, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_62, c_58, c_629])).
% 8.58/3.17  tff(c_36, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.58/3.17  tff(c_50, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.58/3.17  tff(c_331, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.58/3.17  tff(c_339, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_50, c_331])).
% 8.58/3.17  tff(c_354, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_339])).
% 8.58/3.17  tff(c_911, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_576, c_576, c_354])).
% 8.58/3.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.58/3.17  tff(c_42, plain, (![B_36, A_35]: (m1_subset_1(B_36, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_36), A_35))) | ~r1_tarski(k2_relat_1(B_36), A_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.58/3.17  tff(c_1508, plain, (![B_194, A_190, B_191, E_193, A_192]: (k1_partfun1(A_192, B_191, k1_relat_1(B_194), A_190, E_193, B_194)=k5_relat_1(E_193, B_194) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))) | ~v1_funct_1(E_193) | ~r1_tarski(k2_relat_1(B_194), A_190) | ~v1_funct_1(B_194) | ~v1_relat_1(B_194))), inference(resolution, [status(thm)], [c_42, c_510])).
% 8.58/3.17  tff(c_1526, plain, (![B_194, A_190]: (k1_partfun1('#skF_2', '#skF_1', k1_relat_1(B_194), A_190, '#skF_4', B_194)=k5_relat_1('#skF_4', B_194) | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1(B_194), A_190) | ~v1_funct_1(B_194) | ~v1_relat_1(B_194))), inference(resolution, [status(thm)], [c_52, c_1508])).
% 8.58/3.17  tff(c_2237, plain, (![B_240, A_241]: (k1_partfun1('#skF_2', '#skF_1', k1_relat_1(B_240), A_241, '#skF_4', B_240)=k5_relat_1('#skF_4', B_240) | ~r1_tarski(k2_relat_1(B_240), A_241) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1526])).
% 8.58/3.17  tff(c_2248, plain, (![B_240]: (k1_partfun1('#skF_2', '#skF_1', k1_relat_1(B_240), k2_relat_1(B_240), '#skF_4', B_240)=k5_relat_1('#skF_4', B_240) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240))), inference(resolution, [status(thm)], [c_6, c_2237])).
% 8.58/3.17  tff(c_20, plain, (![C_13, B_12, A_11]: (v5_relat_1(C_13, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.58/3.17  tff(c_1233, plain, (![D_177, F_178, B_175, C_174, E_176, A_173]: (v5_relat_1(k1_partfun1(A_173, B_175, C_174, D_177, E_176, F_178), D_177) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(C_174, D_177))) | ~v1_funct_1(F_178) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_173, B_175))) | ~v1_funct_1(E_176))), inference(resolution, [status(thm)], [c_596, c_20])).
% 8.58/3.17  tff(c_5746, plain, (![E_435, A_433, B_436, A_434, B_437]: (v5_relat_1(k1_partfun1(A_434, B_437, k1_relat_1(B_436), A_433, E_435, B_436), A_433) | ~m1_subset_1(E_435, k1_zfmisc_1(k2_zfmisc_1(A_434, B_437))) | ~v1_funct_1(E_435) | ~r1_tarski(k2_relat_1(B_436), A_433) | ~v1_funct_1(B_436) | ~v1_relat_1(B_436))), inference(resolution, [status(thm)], [c_42, c_1233])).
% 8.58/3.17  tff(c_5764, plain, (![B_240]: (v5_relat_1(k5_relat_1('#skF_4', B_240), k2_relat_1(B_240)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1(B_240), k2_relat_1(B_240)) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240))), inference(superposition, [status(thm), theory('equality')], [c_2248, c_5746])).
% 8.58/3.17  tff(c_5829, plain, (![B_445]: (v5_relat_1(k5_relat_1('#skF_4', B_445), k2_relat_1(B_445)) | ~v1_funct_1(B_445) | ~v1_relat_1(B_445))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_52, c_5764])).
% 8.58/3.17  tff(c_5834, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_911, c_5829])).
% 8.58/3.17  tff(c_5840, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_62, c_5834])).
% 8.58/3.17  tff(c_107, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)) | ~v1_relat_1(k2_zfmisc_1(A_27, A_27)))), inference(resolution, [status(thm)], [c_36, c_104])).
% 8.58/3.17  tff(c_116, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_107])).
% 8.58/3.17  tff(c_40, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.58/3.17  tff(c_18, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.58/3.17  tff(c_63, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 8.58/3.17  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.58/3.17  tff(c_124, plain, (![B_51, A_52]: (r1_tarski(k2_relat_1(B_51), A_52) | ~v5_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.58/3.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.58/3.17  tff(c_244, plain, (![B_76, A_77]: (k2_relat_1(B_76)=A_77 | ~r1_tarski(A_77, k2_relat_1(B_76)) | ~v5_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_124, c_2])).
% 8.58/3.17  tff(c_2805, plain, (![B_255, B_254]: (k2_relat_1(B_255)=k2_relat_1(B_254) | ~v5_relat_1(B_254, k2_relat_1(B_255)) | ~v1_relat_1(B_254) | ~v5_relat_1(B_255, k2_relat_1(B_254)) | ~v1_relat_1(B_255))), inference(resolution, [status(thm)], [c_12, c_244])).
% 8.58/3.17  tff(c_2815, plain, (![A_10, B_254]: (k2_relat_1(k6_partfun1(A_10))=k2_relat_1(B_254) | ~v5_relat_1(B_254, A_10) | ~v1_relat_1(B_254) | ~v5_relat_1(k6_partfun1(A_10), k2_relat_1(B_254)) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_2805])).
% 8.58/3.17  tff(c_2825, plain, (![B_254, A_10]: (k2_relat_1(B_254)=A_10 | ~v5_relat_1(B_254, A_10) | ~v1_relat_1(B_254) | ~v5_relat_1(k6_partfun1(A_10), k2_relat_1(B_254)))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_63, c_2815])).
% 8.58/3.17  tff(c_5847, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5840, c_2825])).
% 8.58/3.17  tff(c_5863, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_195, c_5847])).
% 8.58/3.17  tff(c_5865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_5863])).
% 8.58/3.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/3.17  
% 8.58/3.17  Inference rules
% 8.58/3.17  ----------------------
% 8.58/3.17  #Ref     : 0
% 8.58/3.17  #Sup     : 1195
% 8.58/3.17  #Fact    : 0
% 8.58/3.17  #Define  : 0
% 8.58/3.17  #Split   : 0
% 8.58/3.17  #Chain   : 0
% 8.58/3.17  #Close   : 0
% 8.58/3.17  
% 8.58/3.17  Ordering : KBO
% 8.58/3.17  
% 8.58/3.17  Simplification rules
% 8.58/3.17  ----------------------
% 8.58/3.18  #Subsume      : 39
% 8.58/3.18  #Demod        : 1691
% 8.58/3.18  #Tautology    : 284
% 8.58/3.18  #SimpNegUnit  : 2
% 8.58/3.18  #BackRed      : 38
% 8.58/3.18  
% 8.58/3.18  #Partial instantiations: 0
% 8.58/3.18  #Strategies tried      : 1
% 8.79/3.18  
% 8.79/3.18  Timing (in seconds)
% 8.79/3.18  ----------------------
% 8.79/3.18  Preprocessing        : 0.38
% 8.79/3.18  Parsing              : 0.20
% 8.79/3.18  CNF conversion       : 0.03
% 8.79/3.18  Main loop            : 2.02
% 8.79/3.18  Inferencing          : 0.67
% 8.79/3.18  Reduction            : 0.85
% 8.79/3.18  Demodulation         : 0.68
% 8.79/3.18  BG Simplification    : 0.05
% 8.79/3.18  Subsumption          : 0.34
% 8.79/3.18  Abstraction          : 0.07
% 8.79/3.18  MUC search           : 0.00
% 8.79/3.18  Cooper               : 0.00
% 8.79/3.18  Total                : 2.45
% 8.79/3.18  Index Insertion      : 0.00
% 8.79/3.18  Index Deletion       : 0.00
% 8.79/3.18  Index Matching       : 0.00
% 8.79/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
