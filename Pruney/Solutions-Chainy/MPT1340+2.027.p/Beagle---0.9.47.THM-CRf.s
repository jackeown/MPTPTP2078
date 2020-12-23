%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:33 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  132 (15617 expanded)
%              Number of leaves         :   40 (5358 expanded)
%              Depth                    :   23
%              Number of atoms          :  265 (44984 expanded)
%              Number of equality atoms :   66 (12090 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_166,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_63,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_71,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_63])).

tff(c_58,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_70,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_63])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_77,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_52])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_77])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_10])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_149,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_153,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_149])).

tff(c_50,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_97,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_70,c_50])).

tff(c_159,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_97])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_54])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72])).

tff(c_168,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_83])).

tff(c_154,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_154])).

tff(c_184,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_158])).

tff(c_166,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_78])).

tff(c_212,plain,(
    ! [B_59,A_60,C_61] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_60,B_59,C_61) = A_60
      | ~ v1_funct_2(C_61,A_60,B_59)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_215,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_166,c_212])).

tff(c_218,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_184,c_215])).

tff(c_219,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_224,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_168])).

tff(c_222,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_166])).

tff(c_283,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_funct_2(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(D_70,A_68,B_69)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_285,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_222,c_283])).

tff(c_288,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_285])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_164,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_153])).

tff(c_221,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_164])).

tff(c_341,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_tops_2(A_77,B_78,C_79) = k2_funct_1(C_79)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(A_77,B_78,C_79) != B_78
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(C_79,A_77,B_78)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_347,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_222,c_341])).

tff(c_351,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_221,c_48,c_347])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k2_tops_2(A_24,B_25,C_26),k1_zfmisc_1(k2_zfmisc_1(B_25,A_24)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_358,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_38])).

tff(c_362,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_222,c_358])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_407,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_362,c_14])).

tff(c_276,plain,(
    ! [A_65,B_66,C_67] :
      ( v1_funct_1(k2_tops_2(A_65,B_66,C_67))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_funct_2(C_67,A_65,B_66)
      | ~ v1_funct_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_279,plain,
    ( v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_222,c_276])).

tff(c_282,plain,(
    v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_279])).

tff(c_353,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_282])).

tff(c_289,plain,(
    ! [A_71,B_72,C_73] :
      ( v1_funct_2(k2_tops_2(A_71,B_72,C_73),B_72,A_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_291,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_222,c_289])).

tff(c_294,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_291])).

tff(c_352,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_294])).

tff(c_36,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_tops_2(A_21,B_22,C_23) = k2_funct_1(C_23)
      | ~ v2_funct_1(C_23)
      | k2_relset_1(A_21,B_22,C_23) != B_22
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_366,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_362,c_36])).

tff(c_391,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_352,c_366])).

tff(c_496,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_391])).

tff(c_497,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_516,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_497])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56,c_48,c_516])).

tff(c_521,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_544,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_226,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_71])).

tff(c_169,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_70])).

tff(c_453,plain,(
    ! [A_84,B_85,C_86] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_84),u1_struct_0(B_85),C_86))
      | ~ v2_funct_1(C_86)
      | k2_relset_1(u1_struct_0(A_84),u1_struct_0(B_85),C_86) != k2_struct_0(B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),u1_struct_0(B_85))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_84),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ l1_struct_0(B_85)
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_469,plain,(
    ! [A_84,C_86] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_84),u1_struct_0('#skF_2'),C_86))
      | ~ v2_funct_1(C_86)
      | k2_relset_1(u1_struct_0(A_84),u1_struct_0('#skF_2'),C_86) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_84),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_86)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_453])).

tff(c_581,plain,(
    ! [A_98,C_99] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_98),k2_relat_1('#skF_3'),C_99))
      | ~ v2_funct_1(C_99)
      | k2_relset_1(u1_struct_0(A_98),k2_relat_1('#skF_3'),C_99) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_99,u1_struct_0(A_98),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_99)
      | ~ l1_struct_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_169,c_169,c_159,c_169,c_469])).

tff(c_588,plain,(
    ! [C_99] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_99))
      | ~ v2_funct_1(C_99)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_99) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_99,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_99)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_581])).

tff(c_653,plain,(
    ! [C_114] :
      ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_114))
      | ~ v2_funct_1(C_114)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_114) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_114,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_226,c_226,c_226,c_588])).

tff(c_660,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_222,c_653])).

tff(c_664,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224,c_221,c_48,c_351,c_660])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_664])).

tff(c_667,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_46,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_107,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_71,c_70,c_70,c_70,c_46])).

tff(c_165,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_159,c_107])).

tff(c_220,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_219,c_219,c_165])).

tff(c_354,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_220])).

tff(c_671,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_354])).

tff(c_713,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_671])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56,c_48,c_288,c_713])).

tff(c_717,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_84,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_90,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_84])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_90])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_94])).

tff(c_167,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_95])).

tff(c_725,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_167])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.52  
% 3.45/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.53  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.45/1.53  
% 3.45/1.53  %Foreground sorts:
% 3.45/1.53  
% 3.45/1.53  
% 3.45/1.53  %Background operators:
% 3.45/1.53  
% 3.45/1.53  
% 3.45/1.53  %Foreground operators:
% 3.45/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.45/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.45/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.45/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.45/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.53  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.45/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.45/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.45/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.45/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.45/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.53  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.45/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.53  
% 3.60/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.60/1.55  tff(f_166, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.60/1.55  tff(f_94, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.60/1.55  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.55  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.60/1.55  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.60/1.55  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.60/1.55  tff(f_90, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.60/1.55  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.60/1.55  tff(f_36, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.60/1.55  tff(f_114, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.60/1.55  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.60/1.55  tff(f_144, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 3.60/1.55  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.60/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.60/1.55  tff(c_62, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_63, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.60/1.55  tff(c_71, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_63])).
% 3.60/1.55  tff(c_58, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_70, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_63])).
% 3.60/1.55  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_77, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_52])).
% 3.60/1.55  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_77])).
% 3.60/1.55  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.60/1.55  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_10])).
% 3.60/1.55  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_48, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_149, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.55  tff(c_153, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_149])).
% 3.60/1.55  tff(c_50, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_97, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_70, c_50])).
% 3.60/1.55  tff(c_159, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_97])).
% 3.60/1.55  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_54])).
% 3.60/1.55  tff(c_83, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_72])).
% 3.60/1.55  tff(c_168, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_83])).
% 3.60/1.55  tff(c_154, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.60/1.55  tff(c_158, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_154])).
% 3.60/1.55  tff(c_184, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_158])).
% 3.60/1.55  tff(c_166, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_78])).
% 3.60/1.55  tff(c_212, plain, (![B_59, A_60, C_61]: (k1_xboole_0=B_59 | k1_relset_1(A_60, B_59, C_61)=A_60 | ~v1_funct_2(C_61, A_60, B_59) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.60/1.55  tff(c_215, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_166, c_212])).
% 3.60/1.55  tff(c_218, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_184, c_215])).
% 3.60/1.55  tff(c_219, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_218])).
% 3.60/1.55  tff(c_224, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_168])).
% 3.60/1.55  tff(c_222, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_166])).
% 3.60/1.55  tff(c_283, plain, (![A_68, B_69, D_70]: (r2_funct_2(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(D_70, A_68, B_69) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.55  tff(c_285, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_222, c_283])).
% 3.60/1.55  tff(c_288, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_285])).
% 3.60/1.55  tff(c_8, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.60/1.55  tff(c_4, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.60/1.55  tff(c_164, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_153])).
% 3.60/1.55  tff(c_221, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_164])).
% 3.60/1.55  tff(c_341, plain, (![A_77, B_78, C_79]: (k2_tops_2(A_77, B_78, C_79)=k2_funct_1(C_79) | ~v2_funct_1(C_79) | k2_relset_1(A_77, B_78, C_79)!=B_78 | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(C_79, A_77, B_78) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.60/1.55  tff(c_347, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_222, c_341])).
% 3.60/1.55  tff(c_351, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_221, c_48, c_347])).
% 3.60/1.55  tff(c_38, plain, (![A_24, B_25, C_26]: (m1_subset_1(k2_tops_2(A_24, B_25, C_26), k1_zfmisc_1(k2_zfmisc_1(B_25, A_24))) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.60/1.55  tff(c_358, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_351, c_38])).
% 3.60/1.55  tff(c_362, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_222, c_358])).
% 3.60/1.55  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.55  tff(c_407, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_362, c_14])).
% 3.60/1.55  tff(c_276, plain, (![A_65, B_66, C_67]: (v1_funct_1(k2_tops_2(A_65, B_66, C_67)) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_funct_2(C_67, A_65, B_66) | ~v1_funct_1(C_67))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.60/1.55  tff(c_279, plain, (v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_222, c_276])).
% 3.60/1.55  tff(c_282, plain, (v1_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_279])).
% 3.60/1.55  tff(c_353, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_282])).
% 3.60/1.55  tff(c_289, plain, (![A_71, B_72, C_73]: (v1_funct_2(k2_tops_2(A_71, B_72, C_73), B_72, A_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_73, A_71, B_72) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.60/1.55  tff(c_291, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_222, c_289])).
% 3.60/1.55  tff(c_294, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_291])).
% 3.60/1.55  tff(c_352, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_294])).
% 3.60/1.55  tff(c_36, plain, (![A_21, B_22, C_23]: (k2_tops_2(A_21, B_22, C_23)=k2_funct_1(C_23) | ~v2_funct_1(C_23) | k2_relset_1(A_21, B_22, C_23)!=B_22 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.60/1.55  tff(c_366, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_362, c_36])).
% 3.60/1.55  tff(c_391, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_352, c_366])).
% 3.60/1.55  tff(c_496, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_391])).
% 3.60/1.55  tff(c_497, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_496])).
% 3.60/1.55  tff(c_516, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_497])).
% 3.60/1.55  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_56, c_48, c_516])).
% 3.60/1.55  tff(c_521, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_496])).
% 3.60/1.55  tff(c_544, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_521])).
% 3.60/1.55  tff(c_226, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_71])).
% 3.60/1.55  tff(c_169, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_70])).
% 3.60/1.55  tff(c_453, plain, (![A_84, B_85, C_86]: (v2_funct_1(k2_tops_2(u1_struct_0(A_84), u1_struct_0(B_85), C_86)) | ~v2_funct_1(C_86) | k2_relset_1(u1_struct_0(A_84), u1_struct_0(B_85), C_86)!=k2_struct_0(B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), u1_struct_0(B_85)))) | ~v1_funct_2(C_86, u1_struct_0(A_84), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~l1_struct_0(B_85) | ~l1_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.60/1.55  tff(c_469, plain, (![A_84, C_86]: (v2_funct_1(k2_tops_2(u1_struct_0(A_84), u1_struct_0('#skF_2'), C_86)) | ~v2_funct_1(C_86) | k2_relset_1(u1_struct_0(A_84), u1_struct_0('#skF_2'), C_86)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_86, u1_struct_0(A_84), u1_struct_0('#skF_2')) | ~v1_funct_1(C_86) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_169, c_453])).
% 3.60/1.55  tff(c_581, plain, (![A_98, C_99]: (v2_funct_1(k2_tops_2(u1_struct_0(A_98), k2_relat_1('#skF_3'), C_99)) | ~v2_funct_1(C_99) | k2_relset_1(u1_struct_0(A_98), k2_relat_1('#skF_3'), C_99)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_99, u1_struct_0(A_98), k2_relat_1('#skF_3')) | ~v1_funct_1(C_99) | ~l1_struct_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_169, c_169, c_159, c_169, c_469])).
% 3.60/1.55  tff(c_588, plain, (![C_99]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_99)) | ~v2_funct_1(C_99) | k2_relset_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_99)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_99, u1_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_99) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_581])).
% 3.60/1.55  tff(c_653, plain, (![C_114]: (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_114)) | ~v2_funct_1(C_114) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_114)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_114, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_226, c_226, c_226, c_588])).
% 3.60/1.55  tff(c_660, plain, (v2_funct_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_222, c_653])).
% 3.60/1.55  tff(c_664, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224, c_221, c_48, c_351, c_660])).
% 3.60/1.55  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_544, c_664])).
% 3.60/1.55  tff(c_667, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_521])).
% 3.60/1.55  tff(c_46, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_107, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_71, c_70, c_70, c_70, c_46])).
% 3.60/1.55  tff(c_165, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_159, c_107])).
% 3.60/1.55  tff(c_220, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_219, c_219, c_165])).
% 3.60/1.55  tff(c_354, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_220])).
% 3.60/1.55  tff(c_671, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_667, c_354])).
% 3.60/1.55  tff(c_713, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_671])).
% 3.60/1.55  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_56, c_48, c_288, c_713])).
% 3.60/1.55  tff(c_717, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_218])).
% 3.60/1.55  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.60/1.55  tff(c_84, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.60/1.55  tff(c_90, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_84])).
% 3.60/1.55  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_90])).
% 3.60/1.55  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_94])).
% 3.60/1.55  tff(c_167, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_95])).
% 3.60/1.55  tff(c_725, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_717, c_167])).
% 3.60/1.55  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_725])).
% 3.60/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.55  
% 3.60/1.55  Inference rules
% 3.60/1.55  ----------------------
% 3.60/1.55  #Ref     : 0
% 3.60/1.55  #Sup     : 148
% 3.60/1.55  #Fact    : 0
% 3.60/1.55  #Define  : 0
% 3.60/1.55  #Split   : 6
% 3.60/1.55  #Chain   : 0
% 3.60/1.55  #Close   : 0
% 3.60/1.55  
% 3.60/1.55  Ordering : KBO
% 3.60/1.55  
% 3.60/1.55  Simplification rules
% 3.60/1.55  ----------------------
% 3.60/1.55  #Subsume      : 6
% 3.60/1.55  #Demod        : 241
% 3.60/1.55  #Tautology    : 81
% 3.60/1.55  #SimpNegUnit  : 3
% 3.60/1.55  #BackRed      : 34
% 3.60/1.55  
% 3.60/1.55  #Partial instantiations: 0
% 3.60/1.55  #Strategies tried      : 1
% 3.60/1.55  
% 3.60/1.55  Timing (in seconds)
% 3.60/1.55  ----------------------
% 3.60/1.55  Preprocessing        : 0.37
% 3.60/1.55  Parsing              : 0.20
% 3.60/1.55  CNF conversion       : 0.02
% 3.60/1.55  Main loop            : 0.40
% 3.60/1.55  Inferencing          : 0.13
% 3.60/1.55  Reduction            : 0.14
% 3.60/1.55  Demodulation         : 0.10
% 3.60/1.55  BG Simplification    : 0.02
% 3.60/1.55  Subsumption          : 0.07
% 3.60/1.55  Abstraction          : 0.02
% 3.60/1.55  MUC search           : 0.00
% 3.60/1.55  Cooper               : 0.00
% 3.60/1.55  Total                : 0.82
% 3.60/1.55  Index Insertion      : 0.00
% 3.60/1.55  Index Deletion       : 0.00
% 3.60/1.55  Index Matching       : 0.00
% 3.60/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
