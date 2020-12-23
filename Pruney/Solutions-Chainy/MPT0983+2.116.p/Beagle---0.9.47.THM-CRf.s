%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 371 expanded)
%              Number of leaves         :   51 ( 149 expanded)
%              Depth                    :   15
%              Number of atoms          :  269 (1174 expanded)
%              Number of equality atoms :   46 ( 107 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_139,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_85,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_142,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_173,plain,(
    ! [B_72,A_73] :
      ( v1_xboole_0(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_173])).

tff(c_190,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_194,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_190])).

tff(c_62,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1410,plain,(
    ! [C_169,B_172,D_170,E_167,F_171,A_168] :
      ( k1_partfun1(A_168,B_172,C_169,D_170,E_167,F_171) = k5_relat_1(E_167,F_171)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(C_169,D_170)))
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_172)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1420,plain,(
    ! [A_168,B_172,E_167] :
      ( k1_partfun1(A_168,B_172,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_172)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_72,c_1410])).

tff(c_2349,plain,(
    ! [A_207,B_208,E_209] :
      ( k1_partfun1(A_207,B_208,'#skF_2','#skF_1',E_209,'#skF_4') = k5_relat_1(E_209,'#skF_4')
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_1(E_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1420])).

tff(c_2370,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2349])).

tff(c_2378,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2370])).

tff(c_52,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] :
      ( m1_subset_1(k1_partfun1(A_34,B_35,C_36,D_37,E_38,F_39),k1_zfmisc_1(k2_zfmisc_1(A_34,D_37)))
      | ~ m1_subset_1(F_39,k1_zfmisc_1(k2_zfmisc_1(C_36,D_37)))
      | ~ v1_funct_1(F_39)
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(E_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3062,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2378,c_52])).

tff(c_3069,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_3062])).

tff(c_58,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_975,plain,(
    ! [D_134,C_135,A_136,B_137] :
      ( D_134 = C_135
      | ~ r2_relset_1(A_136,B_137,C_135,D_134)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_985,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_975])).

tff(c_1004,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_985])).

tff(c_4126,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3069,c_2378,c_2378,c_1004])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    ! [B_49,A_48,D_51,C_50,E_53] :
      ( k1_xboole_0 = C_50
      | v2_funct_1(D_51)
      | ~ v2_funct_1(k1_partfun1(A_48,B_49,B_49,C_50,D_51,E_53))
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(B_49,C_50)))
      | ~ v1_funct_2(E_53,B_49,C_50)
      | ~ v1_funct_1(E_53)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_51,A_48,B_49)
      | ~ v1_funct_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3059,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2378,c_66])).

tff(c_3066,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_3059])).

tff(c_3067,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_3066])).

tff(c_3071,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3067])).

tff(c_4133,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4126,c_3071])).

tff(c_4144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_4133])).

tff(c_4145,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3067])).

tff(c_98,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_104,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_34])).

tff(c_169,plain,(
    ! [A_71] : m1_subset_1(k6_partfun1(A_71),k1_zfmisc_1(k2_zfmisc_1(A_71,A_71))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_172,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_169])).

tff(c_186,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_172,c_173])).

tff(c_223,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_227,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_223])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_271,plain,(
    ! [B_81,A_82] :
      ( ~ r1_xboole_0(B_81,A_82)
      | ~ r1_tarski(B_81,A_82)
      | v1_xboole_0(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_276,plain,(
    ! [A_83] :
      ( ~ r1_tarski(A_83,k1_xboole_0)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_12,c_271])).

tff(c_280,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_276])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_280])).

tff(c_289,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_4195,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4145,c_289])).

tff(c_4209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_4195])).

tff(c_4210,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4218,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4210,c_2])).

tff(c_117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_83])).

tff(c_4225,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4218,c_117])).

tff(c_4232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_4225])).

tff(c_4233,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4414,plain,(
    ! [B_282,A_283] :
      ( v1_relat_1(B_282)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(A_283))
      | ~ v1_relat_1(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4426,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_4414])).

tff(c_4438,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4426])).

tff(c_4452,plain,(
    ! [C_285,B_286,A_287] :
      ( v5_relat_1(C_285,B_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4467,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_4452])).

tff(c_4423,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_4414])).

tff(c_4435,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4423])).

tff(c_32,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_85,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_5354,plain,(
    ! [F_361,A_358,E_357,C_359,D_360,B_362] :
      ( k1_partfun1(A_358,B_362,C_359,D_360,E_357,F_361) = k5_relat_1(E_357,F_361)
      | ~ m1_subset_1(F_361,k1_zfmisc_1(k2_zfmisc_1(C_359,D_360)))
      | ~ v1_funct_1(F_361)
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(A_358,B_362)))
      | ~ v1_funct_1(E_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5364,plain,(
    ! [A_358,B_362,E_357] :
      ( k1_partfun1(A_358,B_362,'#skF_2','#skF_1',E_357,'#skF_4') = k5_relat_1(E_357,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(A_358,B_362)))
      | ~ v1_funct_1(E_357) ) ),
    inference(resolution,[status(thm)],[c_72,c_5354])).

tff(c_6806,plain,(
    ! [A_425,B_426,E_427] :
      ( k1_partfun1(A_425,B_426,'#skF_2','#skF_1',E_427,'#skF_4') = k5_relat_1(E_427,'#skF_4')
      | ~ m1_subset_1(E_427,k1_zfmisc_1(k2_zfmisc_1(A_425,B_426)))
      | ~ v1_funct_1(E_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5364])).

tff(c_6833,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_6806])).

tff(c_6847,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6833])).

tff(c_7671,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6847,c_52])).

tff(c_7677,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_7671])).

tff(c_4881,plain,(
    ! [D_324,C_325,A_326,B_327] :
      ( D_324 = C_325
      | ~ r2_relset_1(A_326,B_327,C_325,D_324)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4889,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_4881])).

tff(c_4904,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4889])).

tff(c_8077,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7677,c_6847,c_6847,c_4904])).

tff(c_28,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8099,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8077,c_28])).

tff(c_8107,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_4438,c_85,c_8099])).

tff(c_4540,plain,(
    ! [B_300,A_301] :
      ( r1_tarski(k2_relat_1(B_300),A_301)
      | ~ v5_relat_1(B_300,A_301)
      | ~ v1_relat_1(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4563,plain,(
    ! [B_300,A_301] :
      ( k2_relat_1(B_300) = A_301
      | ~ r1_tarski(A_301,k2_relat_1(B_300))
      | ~ v5_relat_1(B_300,A_301)
      | ~ v1_relat_1(B_300) ) ),
    inference(resolution,[status(thm)],[c_4540,c_4])).

tff(c_8111,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8107,c_4563])).

tff(c_8116,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_4467,c_8111])).

tff(c_4493,plain,(
    ! [B_293,A_294] :
      ( v5_relat_1(B_293,A_294)
      | ~ r1_tarski(k2_relat_1(B_293),A_294)
      | ~ v1_relat_1(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4508,plain,(
    ! [B_293] :
      ( v5_relat_1(B_293,k2_relat_1(B_293))
      | ~ v1_relat_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_8,c_4493])).

tff(c_4652,plain,(
    ! [B_305] :
      ( v2_funct_2(B_305,k2_relat_1(B_305))
      | ~ v5_relat_1(B_305,k2_relat_1(B_305))
      | ~ v1_relat_1(B_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4673,plain,(
    ! [B_293] :
      ( v2_funct_2(B_293,k2_relat_1(B_293))
      | ~ v1_relat_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_4508,c_4652])).

tff(c_8138,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8116,c_4673])).

tff(c_8162,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_8138])).

tff(c_8164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4233,c_8162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.41/3.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/3.91  
% 11.41/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/3.91  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.41/3.91  
% 11.41/3.91  %Foreground sorts:
% 11.41/3.91  
% 11.41/3.91  
% 11.41/3.91  %Background operators:
% 11.41/3.91  
% 11.41/3.91  
% 11.41/3.91  %Foreground operators:
% 11.41/3.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.41/3.91  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.41/3.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.41/3.91  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.41/3.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.41/3.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.41/3.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.41/3.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.41/3.91  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.41/3.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.41/3.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.41/3.91  tff('#skF_2', type, '#skF_2': $i).
% 11.41/3.91  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.41/3.91  tff('#skF_3', type, '#skF_3': $i).
% 11.41/3.91  tff('#skF_1', type, '#skF_1': $i).
% 11.41/3.91  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 11.41/3.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.41/3.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.41/3.91  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.41/3.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.41/3.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.41/3.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.41/3.91  tff('#skF_4', type, '#skF_4': $i).
% 11.41/3.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.41/3.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.41/3.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.41/3.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.41/3.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.41/3.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.41/3.91  
% 11.74/3.95  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 11.74/3.95  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 11.74/3.95  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.74/3.95  tff(f_139, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.74/3.95  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 11.74/3.95  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.74/3.95  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.74/3.95  tff(f_127, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.74/3.95  tff(f_103, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.74/3.95  tff(f_161, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 11.74/3.95  tff(f_85, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 11.74/3.95  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.74/3.95  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.74/3.95  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 11.74/3.95  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.74/3.95  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.74/3.95  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.74/3.95  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.74/3.95  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.74/3.95  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 11.74/3.95  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 11.74/3.95  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 11.74/3.95  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_142, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 11.74/3.95  tff(c_16, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.74/3.95  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_173, plain, (![B_72, A_73]: (v1_xboole_0(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.74/3.95  tff(c_188, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_173])).
% 11.74/3.95  tff(c_190, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_188])).
% 11.74/3.95  tff(c_194, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_190])).
% 11.74/3.95  tff(c_62, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.74/3.95  tff(c_38, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.74/3.95  tff(c_83, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 11.74/3.95  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_1410, plain, (![C_169, B_172, D_170, E_167, F_171, A_168]: (k1_partfun1(A_168, B_172, C_169, D_170, E_167, F_171)=k5_relat_1(E_167, F_171) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(C_169, D_170))) | ~v1_funct_1(F_171) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_172))) | ~v1_funct_1(E_167))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.74/3.95  tff(c_1420, plain, (![A_168, B_172, E_167]: (k1_partfun1(A_168, B_172, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_172))) | ~v1_funct_1(E_167))), inference(resolution, [status(thm)], [c_72, c_1410])).
% 11.74/3.95  tff(c_2349, plain, (![A_207, B_208, E_209]: (k1_partfun1(A_207, B_208, '#skF_2', '#skF_1', E_209, '#skF_4')=k5_relat_1(E_209, '#skF_4') | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_1(E_209))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1420])).
% 11.74/3.95  tff(c_2370, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2349])).
% 11.74/3.95  tff(c_2378, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2370])).
% 11.74/3.95  tff(c_52, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (m1_subset_1(k1_partfun1(A_34, B_35, C_36, D_37, E_38, F_39), k1_zfmisc_1(k2_zfmisc_1(A_34, D_37))) | ~m1_subset_1(F_39, k1_zfmisc_1(k2_zfmisc_1(C_36, D_37))) | ~v1_funct_1(F_39) | ~m1_subset_1(E_38, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(E_38))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.74/3.95  tff(c_3062, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2378, c_52])).
% 11.74/3.95  tff(c_3069, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_3062])).
% 11.74/3.95  tff(c_58, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.74/3.95  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_975, plain, (![D_134, C_135, A_136, B_137]: (D_134=C_135 | ~r2_relset_1(A_136, B_137, C_135, D_134) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.74/3.95  tff(c_985, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_975])).
% 11.74/3.95  tff(c_1004, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_985])).
% 11.74/3.95  tff(c_4126, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3069, c_2378, c_2378, c_1004])).
% 11.74/3.95  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.74/3.95  tff(c_66, plain, (![B_49, A_48, D_51, C_50, E_53]: (k1_xboole_0=C_50 | v2_funct_1(D_51) | ~v2_funct_1(k1_partfun1(A_48, B_49, B_49, C_50, D_51, E_53)) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(B_49, C_50))) | ~v1_funct_2(E_53, B_49, C_50) | ~v1_funct_1(E_53) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_51, A_48, B_49) | ~v1_funct_1(D_51))), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.74/3.95  tff(c_3059, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2378, c_66])).
% 11.74/3.95  tff(c_3066, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_3059])).
% 11.74/3.95  tff(c_3067, plain, (k1_xboole_0='#skF_1' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_142, c_3066])).
% 11.74/3.95  tff(c_3071, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3067])).
% 11.74/3.95  tff(c_4133, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4126, c_3071])).
% 11.74/3.95  tff(c_4144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_4133])).
% 11.74/3.95  tff(c_4145, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3067])).
% 11.74/3.95  tff(c_98, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.74/3.95  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.74/3.95  tff(c_104, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_34])).
% 11.74/3.95  tff(c_169, plain, (![A_71]: (m1_subset_1(k6_partfun1(A_71), k1_zfmisc_1(k2_zfmisc_1(A_71, A_71))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.74/3.95  tff(c_172, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_169])).
% 11.74/3.95  tff(c_186, plain, (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_172, c_173])).
% 11.74/3.95  tff(c_223, plain, (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_186])).
% 11.74/3.95  tff(c_227, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_223])).
% 11.74/3.95  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.74/3.95  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.74/3.95  tff(c_271, plain, (![B_81, A_82]: (~r1_xboole_0(B_81, A_82) | ~r1_tarski(B_81, A_82) | v1_xboole_0(B_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.74/3.95  tff(c_276, plain, (![A_83]: (~r1_tarski(A_83, k1_xboole_0) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_12, c_271])).
% 11.74/3.95  tff(c_280, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_276])).
% 11.74/3.95  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_280])).
% 11.74/3.95  tff(c_289, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_186])).
% 11.74/3.95  tff(c_4195, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4145, c_289])).
% 11.74/3.95  tff(c_4209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_4195])).
% 11.74/3.95  tff(c_4210, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_188])).
% 11.74/3.95  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.74/3.95  tff(c_4218, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4210, c_2])).
% 11.74/3.95  tff(c_117, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104, c_83])).
% 11.74/3.95  tff(c_4225, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4218, c_117])).
% 11.74/3.95  tff(c_4232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_4225])).
% 11.74/3.95  tff(c_4233, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 11.74/3.95  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.74/3.95  tff(c_4414, plain, (![B_282, A_283]: (v1_relat_1(B_282) | ~m1_subset_1(B_282, k1_zfmisc_1(A_283)) | ~v1_relat_1(A_283))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.74/3.95  tff(c_4426, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_4414])).
% 11.74/3.95  tff(c_4438, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4426])).
% 11.74/3.95  tff(c_4452, plain, (![C_285, B_286, A_287]: (v5_relat_1(C_285, B_286) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_286))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.74/3.95  tff(c_4467, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_4452])).
% 11.74/3.95  tff(c_4423, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_4414])).
% 11.74/3.95  tff(c_4435, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4423])).
% 11.74/3.95  tff(c_32, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.74/3.95  tff(c_85, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 11.74/3.95  tff(c_5354, plain, (![F_361, A_358, E_357, C_359, D_360, B_362]: (k1_partfun1(A_358, B_362, C_359, D_360, E_357, F_361)=k5_relat_1(E_357, F_361) | ~m1_subset_1(F_361, k1_zfmisc_1(k2_zfmisc_1(C_359, D_360))) | ~v1_funct_1(F_361) | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(A_358, B_362))) | ~v1_funct_1(E_357))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.74/3.95  tff(c_5364, plain, (![A_358, B_362, E_357]: (k1_partfun1(A_358, B_362, '#skF_2', '#skF_1', E_357, '#skF_4')=k5_relat_1(E_357, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(A_358, B_362))) | ~v1_funct_1(E_357))), inference(resolution, [status(thm)], [c_72, c_5354])).
% 11.74/3.95  tff(c_6806, plain, (![A_425, B_426, E_427]: (k1_partfun1(A_425, B_426, '#skF_2', '#skF_1', E_427, '#skF_4')=k5_relat_1(E_427, '#skF_4') | ~m1_subset_1(E_427, k1_zfmisc_1(k2_zfmisc_1(A_425, B_426))) | ~v1_funct_1(E_427))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5364])).
% 11.74/3.95  tff(c_6833, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_6806])).
% 11.74/3.95  tff(c_6847, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6833])).
% 11.74/3.95  tff(c_7671, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6847, c_52])).
% 11.74/3.95  tff(c_7677, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_7671])).
% 11.74/3.95  tff(c_4881, plain, (![D_324, C_325, A_326, B_327]: (D_324=C_325 | ~r2_relset_1(A_326, B_327, C_325, D_324) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.74/3.95  tff(c_4889, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_4881])).
% 11.74/3.95  tff(c_4904, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4889])).
% 11.74/3.95  tff(c_8077, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7677, c_6847, c_6847, c_4904])).
% 11.74/3.95  tff(c_28, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.74/3.95  tff(c_8099, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8077, c_28])).
% 11.74/3.95  tff(c_8107, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_4438, c_85, c_8099])).
% 11.74/3.95  tff(c_4540, plain, (![B_300, A_301]: (r1_tarski(k2_relat_1(B_300), A_301) | ~v5_relat_1(B_300, A_301) | ~v1_relat_1(B_300))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.74/3.95  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.74/3.95  tff(c_4563, plain, (![B_300, A_301]: (k2_relat_1(B_300)=A_301 | ~r1_tarski(A_301, k2_relat_1(B_300)) | ~v5_relat_1(B_300, A_301) | ~v1_relat_1(B_300))), inference(resolution, [status(thm)], [c_4540, c_4])).
% 11.74/3.95  tff(c_8111, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8107, c_4563])).
% 11.74/3.95  tff(c_8116, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_4467, c_8111])).
% 11.74/3.95  tff(c_4493, plain, (![B_293, A_294]: (v5_relat_1(B_293, A_294) | ~r1_tarski(k2_relat_1(B_293), A_294) | ~v1_relat_1(B_293))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.74/3.95  tff(c_4508, plain, (![B_293]: (v5_relat_1(B_293, k2_relat_1(B_293)) | ~v1_relat_1(B_293))), inference(resolution, [status(thm)], [c_8, c_4493])).
% 11.74/3.95  tff(c_4652, plain, (![B_305]: (v2_funct_2(B_305, k2_relat_1(B_305)) | ~v5_relat_1(B_305, k2_relat_1(B_305)) | ~v1_relat_1(B_305))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.74/3.95  tff(c_4673, plain, (![B_293]: (v2_funct_2(B_293, k2_relat_1(B_293)) | ~v1_relat_1(B_293))), inference(resolution, [status(thm)], [c_4508, c_4652])).
% 11.74/3.95  tff(c_8138, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8116, c_4673])).
% 11.74/3.95  tff(c_8162, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_8138])).
% 11.74/3.95  tff(c_8164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4233, c_8162])).
% 11.74/3.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/3.95  
% 11.74/3.95  Inference rules
% 11.74/3.95  ----------------------
% 11.74/3.95  #Ref     : 0
% 11.74/3.95  #Sup     : 1854
% 11.74/3.95  #Fact    : 0
% 11.74/3.95  #Define  : 0
% 11.74/3.95  #Split   : 17
% 11.74/3.95  #Chain   : 0
% 11.74/3.95  #Close   : 0
% 11.74/3.95  
% 11.74/3.95  Ordering : KBO
% 11.74/3.95  
% 11.74/3.95  Simplification rules
% 11.74/3.95  ----------------------
% 11.74/3.95  #Subsume      : 172
% 11.74/3.95  #Demod        : 2098
% 11.74/3.95  #Tautology    : 1030
% 11.74/3.95  #SimpNegUnit  : 8
% 11.74/3.95  #BackRed      : 104
% 11.74/3.95  
% 11.74/3.95  #Partial instantiations: 0
% 11.74/3.95  #Strategies tried      : 1
% 11.74/3.95  
% 11.74/3.95  Timing (in seconds)
% 11.74/3.95  ----------------------
% 11.74/3.95  Preprocessing        : 0.59
% 11.74/3.96  Parsing              : 0.31
% 11.74/3.96  CNF conversion       : 0.04
% 11.74/3.96  Main loop            : 2.42
% 11.74/3.96  Inferencing          : 0.78
% 11.74/3.96  Reduction            : 0.89
% 11.74/3.96  Demodulation         : 0.67
% 11.74/3.96  BG Simplification    : 0.09
% 11.74/3.96  Subsumption          : 0.48
% 11.74/3.96  Abstraction          : 0.10
% 11.74/3.96  MUC search           : 0.00
% 11.74/3.96  Cooper               : 0.00
% 11.74/3.96  Total                : 3.09
% 11.74/3.96  Index Insertion      : 0.00
% 11.74/3.96  Index Deletion       : 0.00
% 11.74/3.96  Index Matching       : 0.00
% 11.74/3.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
