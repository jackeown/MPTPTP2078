%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:36 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  206 (169534 expanded)
%              Number of leaves         :   57 (58842 expanded)
%              Depth                    :   35
%              Number of atoms          :  510 (485180 expanded)
%              Number of equality atoms :   97 (104796 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_270,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_228,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_236,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_184,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_176,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_198,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_214,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

tff(f_224,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_152,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_248,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_98,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_102,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_110,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_102])).

tff(c_94,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_102])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_145,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_109,c_88])).

tff(c_316,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_324,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_316])).

tff(c_86,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_146,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_109,c_86])).

tff(c_325,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_146])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_123,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(u1_struct_0(A_62))
      | ~ l1_struct_0(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_129,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_123])).

tff(c_133,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_129])).

tff(c_134,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_133])).

tff(c_334,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_134])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_158,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_161,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_145,c_158])).

tff(c_164,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_161])).

tff(c_183,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_187,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_145,c_183])).

tff(c_212,plain,(
    ! [B_82,A_83] :
      ( k1_relat_1(B_82) = A_83
      | ~ v1_partfun1(B_82,A_83)
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_215,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_212])).

tff(c_218,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_215])).

tff(c_219,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_90,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_115,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_90])).

tff(c_116,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_115])).

tff(c_335,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_116])).

tff(c_333,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_145])).

tff(c_461,plain,(
    ! [C_104,A_105,B_106] :
      ( v1_partfun1(C_104,A_105)
      | ~ v1_funct_2(C_104,A_105,B_106)
      | ~ v1_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | v1_xboole_0(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_464,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_333,c_461])).

tff(c_470,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_335,c_464])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_219,c_470])).

tff(c_473,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_478,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_145])).

tff(c_626,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_634,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_478,c_626])).

tff(c_477,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_146])).

tff(c_635,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_477])).

tff(c_480,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_116])).

tff(c_642,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_480])).

tff(c_643,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_478])).

tff(c_1442,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( r2_funct_2(A_175,B_176,C_177,C_177)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_2(D_178,A_175,B_176)
      | ~ v1_funct_1(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_2(C_177,A_175,B_176)
      | ~ v1_funct_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1450,plain,(
    ! [C_177] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_177,C_177)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_177,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_177) ) ),
    inference(resolution,[status(thm)],[c_643,c_1442])).

tff(c_1467,plain,(
    ! [C_179] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_179,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_179,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_1450])).

tff(c_1472,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_643,c_1467])).

tff(c_1479,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_1472])).

tff(c_84,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_640,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_634])).

tff(c_916,plain,(
    ! [C_145,A_146,B_147] :
      ( v1_funct_1(k2_funct_1(C_145))
      | k2_relset_1(A_146,B_147,C_145) != B_147
      | ~ v2_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_2(C_145,A_146,B_147)
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_919,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_643,c_916])).

tff(c_925,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_84,c_640,c_919])).

tff(c_1015,plain,(
    ! [C_157,B_158,A_159] :
      ( v1_funct_2(k2_funct_1(C_157),B_158,A_159)
      | k2_relset_1(A_159,B_158,C_157) != B_158
      | ~ v2_funct_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158)))
      | ~ v1_funct_2(C_157,A_159,B_158)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1018,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_643,c_1015])).

tff(c_1024,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_84,c_640,c_1018])).

tff(c_1220,plain,(
    ! [C_168,B_169,A_170] :
      ( m1_subset_1(k2_funct_1(C_168),k1_zfmisc_1(k2_zfmisc_1(B_169,A_170)))
      | k2_relset_1(A_170,B_169,C_168) != B_169
      | ~ v2_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_2(C_168,A_170,B_169)
      | ~ v1_funct_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1244,plain,(
    ! [C_168,B_169,A_170] :
      ( v1_relat_1(k2_funct_1(C_168))
      | ~ v1_relat_1(k2_zfmisc_1(B_169,A_170))
      | k2_relset_1(A_170,B_169,C_168) != B_169
      | ~ v2_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_2(C_168,A_170,B_169)
      | ~ v1_funct_1(C_168) ) ),
    inference(resolution,[status(thm)],[c_1220,c_8])).

tff(c_1255,plain,(
    ! [C_171,A_172,B_173] :
      ( v1_relat_1(k2_funct_1(C_171))
      | k2_relset_1(A_172,B_173,C_171) != B_173
      | ~ v2_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(C_171,A_172,B_173)
      | ~ v1_funct_1(C_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1244])).

tff(c_1267,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_643,c_1255])).

tff(c_1276,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_84,c_640,c_1267])).

tff(c_20,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(k2_funct_1(B_18),A_17) = k9_relat_1(B_18,A_17)
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_486,plain,(
    ! [A_107] :
      ( k2_relat_1(k2_funct_1(A_107)) = k1_relat_1(A_107)
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_795,plain,(
    ! [A_130] :
      ( k10_relat_1(k2_funct_1(A_130),k1_relat_1(A_130)) = k1_relat_1(k2_funct_1(A_130))
      | ~ v1_relat_1(k2_funct_1(A_130))
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_14])).

tff(c_1278,plain,(
    ! [B_174] :
      ( k9_relat_1(B_174,k1_relat_1(B_174)) = k1_relat_1(k2_funct_1(B_174))
      | ~ v1_relat_1(k2_funct_1(B_174))
      | ~ v2_funct_1(B_174)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174)
      | ~ v2_funct_1(B_174)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_795])).

tff(c_1280,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1276,c_1278])).

tff(c_1285,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_92,c_84,c_1280])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ r1_tarski(k1_relat_1(B_78),A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_199,plain,(
    ! [B_80] :
      ( k7_relat_1(B_80,k1_relat_1(B_80)) = B_80
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    ! [B_80] :
      ( k9_relat_1(B_80,k1_relat_1(B_80)) = k2_relat_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_12])).

tff(c_1305,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_205])).

tff(c_1322,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_164,c_1305])).

tff(c_1377,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_205])).

tff(c_1429,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_1276,c_1377])).

tff(c_2211,plain,(
    ! [A_191] :
      ( k9_relat_1(A_191,k1_relat_1(A_191)) = k1_relat_1(k2_funct_1(A_191))
      | ~ v2_funct_1(A_191)
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(resolution,[status(thm)],[c_20,c_1278])).

tff(c_2250,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_2211])).

tff(c_2267,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_925,c_1429,c_2250])).

tff(c_2268,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2267])).

tff(c_2271,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2268])).

tff(c_2275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_92,c_84,c_2271])).

tff(c_2276,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2267])).

tff(c_198,plain,(
    ! [B_78] :
      ( k7_relat_1(B_78,k1_relat_1(B_78)) = B_78
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_2360,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2276,c_198])).

tff(c_2406,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2360])).

tff(c_2412,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_2406])).

tff(c_2416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_925,c_2412])).

tff(c_2418,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2360])).

tff(c_38,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2277,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2267])).

tff(c_44,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_relat_1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_758,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v2_funct_1(B_125)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2538,plain,(
    ! [A_193] :
      ( v1_relat_1(k6_relat_1(k1_relat_1(A_193)))
      | ~ v2_funct_1(k2_funct_1(A_193))
      | ~ v1_funct_1(k2_funct_1(A_193))
      | ~ v1_relat_1(k2_funct_1(A_193))
      | ~ v2_funct_1(A_193)
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193)
      | ~ v2_funct_1(A_193)
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_758])).

tff(c_2547,plain,
    ( v1_relat_1(k6_relat_1(k2_relat_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_2538])).

tff(c_2559,plain,
    ( v1_relat_1(k6_relat_1(k2_relat_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_925,c_2277,c_1276,c_925,c_2277,c_2418,c_2547])).

tff(c_2713,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2559])).

tff(c_2716,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_2713])).

tff(c_2720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_925,c_2716])).

tff(c_2722,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2559])).

tff(c_578,plain,(
    ! [A_110] :
      ( m1_subset_1(A_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_110),k2_relat_1(A_110))))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    ! [C_29,A_27,B_28] :
      ( v4_relat_1(C_29,A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_602,plain,(
    ! [A_111] :
      ( v4_relat_1(A_111,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_578,c_50])).

tff(c_58,plain,(
    ! [B_38] :
      ( v1_partfun1(B_38,k1_relat_1(B_38))
      | ~ v4_relat_1(B_38,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_614,plain,(
    ! [A_111] :
      ( v1_partfun1(A_111,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_602,c_58])).

tff(c_2342,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2276,c_614])).

tff(c_2841,plain,(
    v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2722,c_2342])).

tff(c_2844,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2841])).

tff(c_2846,plain,(
    v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_92,c_84,c_2844])).

tff(c_597,plain,(
    ! [A_110] :
      ( v4_relat_1(A_110,k1_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_578,c_50])).

tff(c_2345,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2276,c_597])).

tff(c_2850,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2722,c_2345])).

tff(c_2856,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2850])).

tff(c_2861,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_92,c_84,c_2856])).

tff(c_60,plain,(
    ! [B_38,A_37] :
      ( k1_relat_1(B_38) = A_37
      | ~ v1_partfun1(B_38,A_37)
      | ~ v4_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2864,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2861,c_60])).

tff(c_2867,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2846,c_2276,c_2864])).

tff(c_70,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46))))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_633,plain,(
    ! [A_46] :
      ( k2_relset_1(k1_relat_1(A_46),k2_relat_1(A_46),A_46) = k2_relat_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_70,c_626])).

tff(c_1362,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_633])).

tff(c_1418,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_925,c_1362])).

tff(c_2878,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2867,c_2867,c_1418])).

tff(c_953,plain,(
    ! [A_152,B_153] :
      ( k2_funct_1(A_152) = B_153
      | k6_relat_1(k2_relat_1(A_152)) != k5_relat_1(B_153,A_152)
      | k2_relat_1(B_153) != k1_relat_1(A_152)
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4176,plain,(
    ! [A_209] :
      ( k2_funct_1(k2_funct_1(A_209)) = A_209
      | k6_relat_1(k2_relat_1(k2_funct_1(A_209))) != k6_relat_1(k1_relat_1(A_209))
      | k1_relat_1(k2_funct_1(A_209)) != k2_relat_1(A_209)
      | ~ v2_funct_1(k2_funct_1(A_209))
      | ~ v1_funct_1(A_209)
      | ~ v1_relat_1(A_209)
      | ~ v1_funct_1(k2_funct_1(A_209))
      | ~ v1_relat_1(k2_funct_1(A_209))
      | ~ v2_funct_1(A_209)
      | ~ v1_funct_1(A_209)
      | ~ v1_relat_1(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_953])).

tff(c_4182,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2867,c_4176])).

tff(c_4190,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_92,c_84,c_1276,c_925,c_2277,c_1322,c_4182])).

tff(c_80,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_tops_2(A_49,B_50,C_51) = k2_funct_1(C_51)
      | ~ v2_funct_1(C_51)
      | k2_relset_1(A_49,B_50,C_51) != B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_4778,plain,(
    ! [B_222,A_223,C_224] :
      ( k2_tops_2(B_222,A_223,k2_funct_1(C_224)) = k2_funct_1(k2_funct_1(C_224))
      | ~ v2_funct_1(k2_funct_1(C_224))
      | k2_relset_1(B_222,A_223,k2_funct_1(C_224)) != A_223
      | ~ v1_funct_2(k2_funct_1(C_224),B_222,A_223)
      | ~ v1_funct_1(k2_funct_1(C_224))
      | k2_relset_1(A_223,B_222,C_224) != B_222
      | ~ v2_funct_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222)))
      | ~ v1_funct_2(C_224,A_223,B_222)
      | ~ v1_funct_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_1220,c_80])).

tff(c_4796,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_643,c_4778])).

tff(c_4809,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_84,c_640,c_925,c_1024,c_2878,c_2277,c_4190,c_4796])).

tff(c_1156,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_tops_2(A_164,B_165,C_166) = k2_funct_1(C_166)
      | ~ v2_funct_1(C_166)
      | k2_relset_1(A_164,B_165,C_166) != B_165
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_2(C_166,A_164,B_165)
      | ~ v1_funct_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1162,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_643,c_1156])).

tff(c_1169,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642,c_640,c_84,c_1162])).

tff(c_82,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_188,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_110,c_109,c_109,c_109,c_82])).

tff(c_476,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_473,c_188])).

tff(c_641,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_635,c_635,c_476])).

tff(c_1171,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_641])).

tff(c_4811,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4809,c_1171])).

tff(c_4814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_4811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:53:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.41  
% 7.18/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.42  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.18/2.42  
% 7.18/2.42  %Foreground sorts:
% 7.18/2.42  
% 7.18/2.42  
% 7.18/2.42  %Background operators:
% 7.18/2.42  
% 7.18/2.42  
% 7.18/2.42  %Foreground operators:
% 7.18/2.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.18/2.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.18/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.18/2.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.18/2.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.18/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.18/2.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.18/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.18/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.18/2.42  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.18/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.18/2.42  tff('#skF_2', type, '#skF_2': $i).
% 7.18/2.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.18/2.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.18/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.18/2.42  tff('#skF_1', type, '#skF_1': $i).
% 7.18/2.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.18/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.18/2.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.18/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.18/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.18/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.18/2.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.18/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.18/2.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.18/2.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.18/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.18/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.18/2.42  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.18/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.18/2.42  
% 7.18/2.45  tff(f_270, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 7.18/2.45  tff(f_228, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.18/2.45  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.18/2.45  tff(f_236, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.18/2.45  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.18/2.45  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.18/2.45  tff(f_158, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.18/2.45  tff(f_184, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 7.18/2.45  tff(f_176, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.18/2.45  tff(f_198, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 7.18/2.45  tff(f_214, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.18/2.45  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.18/2.45  tff(f_74, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 7.18/2.45  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 7.18/2.45  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.18/2.45  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.18/2.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.18/2.45  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.18/2.45  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.18/2.45  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.18/2.45  tff(f_90, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_funct_1)).
% 7.18/2.45  tff(f_224, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.18/2.45  tff(f_152, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 7.18/2.45  tff(f_248, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 7.18/2.45  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_98, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_102, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_228])).
% 7.18/2.45  tff(c_110, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_98, c_102])).
% 7.18/2.45  tff(c_94, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_94, c_102])).
% 7.18/2.45  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_145, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_109, c_88])).
% 7.18/2.45  tff(c_316, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.18/2.45  tff(c_324, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_145, c_316])).
% 7.18/2.45  tff(c_86, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_146, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_109, c_86])).
% 7.18/2.45  tff(c_325, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_146])).
% 7.18/2.45  tff(c_96, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_123, plain, (![A_62]: (~v1_xboole_0(u1_struct_0(A_62)) | ~l1_struct_0(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.18/2.45  tff(c_129, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_123])).
% 7.18/2.45  tff(c_133, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_129])).
% 7.18/2.45  tff(c_134, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_96, c_133])).
% 7.18/2.45  tff(c_334, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_134])).
% 7.18/2.45  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.18/2.45  tff(c_158, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.45  tff(c_161, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_145, c_158])).
% 7.18/2.45  tff(c_164, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_161])).
% 7.18/2.45  tff(c_183, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.18/2.45  tff(c_187, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_145, c_183])).
% 7.18/2.45  tff(c_212, plain, (![B_82, A_83]: (k1_relat_1(B_82)=A_83 | ~v1_partfun1(B_82, A_83) | ~v4_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.18/2.45  tff(c_215, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_212])).
% 7.18/2.45  tff(c_218, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_215])).
% 7.18/2.45  tff(c_219, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_218])).
% 7.18/2.45  tff(c_90, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_115, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_90])).
% 7.18/2.45  tff(c_116, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_115])).
% 7.18/2.45  tff(c_335, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_116])).
% 7.18/2.45  tff(c_333, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_145])).
% 7.18/2.45  tff(c_461, plain, (![C_104, A_105, B_106]: (v1_partfun1(C_104, A_105) | ~v1_funct_2(C_104, A_105, B_106) | ~v1_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | v1_xboole_0(B_106))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.18/2.45  tff(c_464, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_333, c_461])).
% 7.18/2.45  tff(c_470, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_335, c_464])).
% 7.18/2.45  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_219, c_470])).
% 7.18/2.45  tff(c_473, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_218])).
% 7.18/2.45  tff(c_478, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_145])).
% 7.18/2.45  tff(c_626, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.18/2.45  tff(c_634, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_478, c_626])).
% 7.18/2.45  tff(c_477, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_146])).
% 7.18/2.45  tff(c_635, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_477])).
% 7.18/2.45  tff(c_480, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_116])).
% 7.18/2.45  tff(c_642, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_480])).
% 7.18/2.45  tff(c_643, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_478])).
% 7.18/2.45  tff(c_1442, plain, (![A_175, B_176, C_177, D_178]: (r2_funct_2(A_175, B_176, C_177, C_177) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_2(D_178, A_175, B_176) | ~v1_funct_1(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_2(C_177, A_175, B_176) | ~v1_funct_1(C_177))), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.18/2.45  tff(c_1450, plain, (![C_177]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_177, C_177) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_177, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_177))), inference(resolution, [status(thm)], [c_643, c_1442])).
% 7.18/2.45  tff(c_1467, plain, (![C_179]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_179, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_179, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_179))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_1450])).
% 7.18/2.45  tff(c_1472, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_643, c_1467])).
% 7.18/2.45  tff(c_1479, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_1472])).
% 7.18/2.45  tff(c_84, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_640, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_634])).
% 7.18/2.45  tff(c_916, plain, (![C_145, A_146, B_147]: (v1_funct_1(k2_funct_1(C_145)) | k2_relset_1(A_146, B_147, C_145)!=B_147 | ~v2_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_2(C_145, A_146, B_147) | ~v1_funct_1(C_145))), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.18/2.45  tff(c_919, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_643, c_916])).
% 7.18/2.45  tff(c_925, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_84, c_640, c_919])).
% 7.18/2.45  tff(c_1015, plain, (![C_157, B_158, A_159]: (v1_funct_2(k2_funct_1(C_157), B_158, A_159) | k2_relset_1(A_159, B_158, C_157)!=B_158 | ~v2_funct_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))) | ~v1_funct_2(C_157, A_159, B_158) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.18/2.45  tff(c_1018, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_643, c_1015])).
% 7.18/2.45  tff(c_1024, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_84, c_640, c_1018])).
% 7.18/2.45  tff(c_1220, plain, (![C_168, B_169, A_170]: (m1_subset_1(k2_funct_1(C_168), k1_zfmisc_1(k2_zfmisc_1(B_169, A_170))) | k2_relset_1(A_170, B_169, C_168)!=B_169 | ~v2_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_2(C_168, A_170, B_169) | ~v1_funct_1(C_168))), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.18/2.45  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.45  tff(c_1244, plain, (![C_168, B_169, A_170]: (v1_relat_1(k2_funct_1(C_168)) | ~v1_relat_1(k2_zfmisc_1(B_169, A_170)) | k2_relset_1(A_170, B_169, C_168)!=B_169 | ~v2_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_2(C_168, A_170, B_169) | ~v1_funct_1(C_168))), inference(resolution, [status(thm)], [c_1220, c_8])).
% 7.18/2.45  tff(c_1255, plain, (![C_171, A_172, B_173]: (v1_relat_1(k2_funct_1(C_171)) | k2_relset_1(A_172, B_173, C_171)!=B_173 | ~v2_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(C_171, A_172, B_173) | ~v1_funct_1(C_171))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1244])).
% 7.18/2.45  tff(c_1267, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_643, c_1255])).
% 7.18/2.45  tff(c_1276, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_84, c_640, c_1267])).
% 7.18/2.45  tff(c_20, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.18/2.45  tff(c_22, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.18/2.45  tff(c_32, plain, (![B_18, A_17]: (k10_relat_1(k2_funct_1(B_18), A_17)=k9_relat_1(B_18, A_17) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.18/2.45  tff(c_486, plain, (![A_107]: (k2_relat_1(k2_funct_1(A_107))=k1_relat_1(A_107) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.18/2.45  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.18/2.45  tff(c_795, plain, (![A_130]: (k10_relat_1(k2_funct_1(A_130), k1_relat_1(A_130))=k1_relat_1(k2_funct_1(A_130)) | ~v1_relat_1(k2_funct_1(A_130)) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_486, c_14])).
% 7.18/2.45  tff(c_1278, plain, (![B_174]: (k9_relat_1(B_174, k1_relat_1(B_174))=k1_relat_1(k2_funct_1(B_174)) | ~v1_relat_1(k2_funct_1(B_174)) | ~v2_funct_1(B_174) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174) | ~v2_funct_1(B_174) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_32, c_795])).
% 7.18/2.45  tff(c_1280, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1276, c_1278])).
% 7.18/2.45  tff(c_1285, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_92, c_84, c_1280])).
% 7.18/2.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.45  tff(c_193, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~r1_tarski(k1_relat_1(B_78), A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.18/2.45  tff(c_199, plain, (![B_80]: (k7_relat_1(B_80, k1_relat_1(B_80))=B_80 | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_6, c_193])).
% 7.18/2.45  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.18/2.45  tff(c_205, plain, (![B_80]: (k9_relat_1(B_80, k1_relat_1(B_80))=k2_relat_1(B_80) | ~v1_relat_1(B_80) | ~v1_relat_1(B_80))), inference(superposition, [status(thm), theory('equality')], [c_199, c_12])).
% 7.18/2.45  tff(c_1305, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1285, c_205])).
% 7.18/2.45  tff(c_1322, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_164, c_1305])).
% 7.18/2.45  tff(c_1377, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_205])).
% 7.18/2.45  tff(c_1429, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_1276, c_1377])).
% 7.18/2.45  tff(c_2211, plain, (![A_191]: (k9_relat_1(A_191, k1_relat_1(A_191))=k1_relat_1(k2_funct_1(A_191)) | ~v2_funct_1(A_191) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(resolution, [status(thm)], [c_20, c_1278])).
% 7.18/2.45  tff(c_2250, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_2211])).
% 7.18/2.45  tff(c_2267, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_925, c_1429, c_2250])).
% 7.18/2.45  tff(c_2268, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2267])).
% 7.18/2.45  tff(c_2271, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2268])).
% 7.18/2.45  tff(c_2275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_92, c_84, c_2271])).
% 7.18/2.45  tff(c_2276, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2267])).
% 7.18/2.45  tff(c_198, plain, (![B_78]: (k7_relat_1(B_78, k1_relat_1(B_78))=B_78 | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_6, c_193])).
% 7.18/2.45  tff(c_2360, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2276, c_198])).
% 7.18/2.45  tff(c_2406, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2360])).
% 7.18/2.45  tff(c_2412, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_2406])).
% 7.18/2.45  tff(c_2416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1276, c_925, c_2412])).
% 7.18/2.45  tff(c_2418, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2360])).
% 7.18/2.45  tff(c_38, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.18/2.45  tff(c_18, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.18/2.45  tff(c_2277, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2267])).
% 7.18/2.45  tff(c_44, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_relat_1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.18/2.45  tff(c_758, plain, (![A_124, B_125]: (v1_relat_1(k5_relat_1(A_124, B_125)) | ~v2_funct_1(B_125) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.18/2.45  tff(c_2538, plain, (![A_193]: (v1_relat_1(k6_relat_1(k1_relat_1(A_193))) | ~v2_funct_1(k2_funct_1(A_193)) | ~v1_funct_1(k2_funct_1(A_193)) | ~v1_relat_1(k2_funct_1(A_193)) | ~v2_funct_1(A_193) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193) | ~v2_funct_1(A_193) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_44, c_758])).
% 7.18/2.45  tff(c_2547, plain, (v1_relat_1(k6_relat_1(k2_relat_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_2538])).
% 7.18/2.45  tff(c_2559, plain, (v1_relat_1(k6_relat_1(k2_relat_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_925, c_2277, c_1276, c_925, c_2277, c_2418, c_2547])).
% 7.18/2.45  tff(c_2713, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2559])).
% 7.18/2.45  tff(c_2716, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_2713])).
% 7.18/2.45  tff(c_2720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1276, c_925, c_2716])).
% 7.18/2.45  tff(c_2722, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2559])).
% 7.18/2.45  tff(c_578, plain, (![A_110]: (m1_subset_1(A_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_110), k2_relat_1(A_110)))) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_224])).
% 7.18/2.45  tff(c_50, plain, (![C_29, A_27, B_28]: (v4_relat_1(C_29, A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.18/2.45  tff(c_602, plain, (![A_111]: (v4_relat_1(A_111, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_578, c_50])).
% 7.18/2.45  tff(c_58, plain, (![B_38]: (v1_partfun1(B_38, k1_relat_1(B_38)) | ~v4_relat_1(B_38, k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.18/2.45  tff(c_614, plain, (![A_111]: (v1_partfun1(A_111, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_602, c_58])).
% 7.18/2.45  tff(c_2342, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2276, c_614])).
% 7.18/2.45  tff(c_2841, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2722, c_2342])).
% 7.18/2.45  tff(c_2844, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2841])).
% 7.18/2.45  tff(c_2846, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_92, c_84, c_2844])).
% 7.18/2.45  tff(c_597, plain, (![A_110]: (v4_relat_1(A_110, k1_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_578, c_50])).
% 7.18/2.45  tff(c_2345, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2276, c_597])).
% 7.18/2.45  tff(c_2850, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2722, c_2345])).
% 7.18/2.45  tff(c_2856, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2850])).
% 7.18/2.45  tff(c_2861, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_92, c_84, c_2856])).
% 7.18/2.45  tff(c_60, plain, (![B_38, A_37]: (k1_relat_1(B_38)=A_37 | ~v1_partfun1(B_38, A_37) | ~v4_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.18/2.45  tff(c_2864, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2861, c_60])).
% 7.18/2.45  tff(c_2867, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2846, c_2276, c_2864])).
% 7.18/2.45  tff(c_70, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46)))) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_224])).
% 7.18/2.45  tff(c_633, plain, (![A_46]: (k2_relset_1(k1_relat_1(A_46), k2_relat_1(A_46), A_46)=k2_relat_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_70, c_626])).
% 7.18/2.45  tff(c_1362, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_633])).
% 7.18/2.45  tff(c_1418, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_925, c_1362])).
% 7.18/2.45  tff(c_2878, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2867, c_2867, c_1418])).
% 7.18/2.45  tff(c_953, plain, (![A_152, B_153]: (k2_funct_1(A_152)=B_153 | k6_relat_1(k2_relat_1(A_152))!=k5_relat_1(B_153, A_152) | k2_relat_1(B_153)!=k1_relat_1(A_152) | ~v2_funct_1(A_152) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.18/2.45  tff(c_4176, plain, (![A_209]: (k2_funct_1(k2_funct_1(A_209))=A_209 | k6_relat_1(k2_relat_1(k2_funct_1(A_209)))!=k6_relat_1(k1_relat_1(A_209)) | k1_relat_1(k2_funct_1(A_209))!=k2_relat_1(A_209) | ~v2_funct_1(k2_funct_1(A_209)) | ~v1_funct_1(A_209) | ~v1_relat_1(A_209) | ~v1_funct_1(k2_funct_1(A_209)) | ~v1_relat_1(k2_funct_1(A_209)) | ~v2_funct_1(A_209) | ~v1_funct_1(A_209) | ~v1_relat_1(A_209))), inference(superposition, [status(thm), theory('equality')], [c_44, c_953])).
% 7.18/2.45  tff(c_4182, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2867, c_4176])).
% 7.18/2.45  tff(c_4190, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_92, c_84, c_1276, c_925, c_2277, c_1322, c_4182])).
% 7.18/2.45  tff(c_80, plain, (![A_49, B_50, C_51]: (k2_tops_2(A_49, B_50, C_51)=k2_funct_1(C_51) | ~v2_funct_1(C_51) | k2_relset_1(A_49, B_50, C_51)!=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_51, A_49, B_50) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.18/2.45  tff(c_4778, plain, (![B_222, A_223, C_224]: (k2_tops_2(B_222, A_223, k2_funct_1(C_224))=k2_funct_1(k2_funct_1(C_224)) | ~v2_funct_1(k2_funct_1(C_224)) | k2_relset_1(B_222, A_223, k2_funct_1(C_224))!=A_223 | ~v1_funct_2(k2_funct_1(C_224), B_222, A_223) | ~v1_funct_1(k2_funct_1(C_224)) | k2_relset_1(A_223, B_222, C_224)!=B_222 | ~v2_funct_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))) | ~v1_funct_2(C_224, A_223, B_222) | ~v1_funct_1(C_224))), inference(resolution, [status(thm)], [c_1220, c_80])).
% 7.18/2.45  tff(c_4796, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_643, c_4778])).
% 7.18/2.45  tff(c_4809, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_84, c_640, c_925, c_1024, c_2878, c_2277, c_4190, c_4796])).
% 7.18/2.45  tff(c_1156, plain, (![A_164, B_165, C_166]: (k2_tops_2(A_164, B_165, C_166)=k2_funct_1(C_166) | ~v2_funct_1(C_166) | k2_relset_1(A_164, B_165, C_166)!=B_165 | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_2(C_166, A_164, B_165) | ~v1_funct_1(C_166))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.18/2.45  tff(c_1162, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_643, c_1156])).
% 7.18/2.45  tff(c_1169, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642, c_640, c_84, c_1162])).
% 7.18/2.45  tff(c_82, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.18/2.45  tff(c_188, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_110, c_109, c_109, c_109, c_82])).
% 7.18/2.45  tff(c_476, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_473, c_188])).
% 7.18/2.45  tff(c_641, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_635, c_635, c_476])).
% 7.18/2.45  tff(c_1171, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1169, c_641])).
% 7.18/2.45  tff(c_4811, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4809, c_1171])).
% 7.18/2.45  tff(c_4814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1479, c_4811])).
% 7.18/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.45  
% 7.18/2.45  Inference rules
% 7.18/2.45  ----------------------
% 7.18/2.45  #Ref     : 0
% 7.18/2.45  #Sup     : 1044
% 7.18/2.45  #Fact    : 0
% 7.18/2.45  #Define  : 0
% 7.18/2.45  #Split   : 11
% 7.18/2.45  #Chain   : 0
% 7.18/2.45  #Close   : 0
% 7.18/2.45  
% 7.18/2.45  Ordering : KBO
% 7.18/2.45  
% 7.18/2.45  Simplification rules
% 7.18/2.45  ----------------------
% 7.18/2.45  #Subsume      : 41
% 7.18/2.45  #Demod        : 2486
% 7.18/2.45  #Tautology    : 534
% 7.18/2.45  #SimpNegUnit  : 12
% 7.18/2.45  #BackRed      : 80
% 7.18/2.45  
% 7.18/2.45  #Partial instantiations: 0
% 7.18/2.45  #Strategies tried      : 1
% 7.18/2.45  
% 7.18/2.45  Timing (in seconds)
% 7.18/2.45  ----------------------
% 7.18/2.45  Preprocessing        : 0.41
% 7.18/2.45  Parsing              : 0.22
% 7.18/2.45  CNF conversion       : 0.03
% 7.18/2.45  Main loop            : 1.23
% 7.18/2.45  Inferencing          : 0.40
% 7.18/2.45  Reduction            : 0.48
% 7.18/2.45  Demodulation         : 0.37
% 7.18/2.45  BG Simplification    : 0.06
% 7.18/2.45  Subsumption          : 0.20
% 7.18/2.45  Abstraction          : 0.06
% 7.18/2.45  MUC search           : 0.00
% 7.18/2.45  Cooper               : 0.00
% 7.18/2.45  Total                : 1.71
% 7.18/2.45  Index Insertion      : 0.00
% 7.18/2.45  Index Deletion       : 0.00
% 7.18/2.45  Index Matching       : 0.00
% 7.18/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
