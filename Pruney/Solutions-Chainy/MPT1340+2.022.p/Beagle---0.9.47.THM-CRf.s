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
% DateTime   : Thu Dec  3 10:23:32 EST 2020

% Result     : Theorem 11.70s
% Output     : CNFRefutation 11.70s
% Verified   : 
% Statistics : Number of formulae       :  308 (279732 expanded)
%              Number of leaves         :   52 (97233 expanded)
%              Depth                    :   42
%              Number of atoms          :  757 (811096 expanded)
%              Number of equality atoms :  179 (206172 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_214,negated_conjecture,(
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

tff(f_172,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_140,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_168,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_192,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_180,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_94,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_150,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_158,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_150])).

tff(c_90,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_157,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_150])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_169,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_157,c_84])).

tff(c_215,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_232,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_215])).

tff(c_80,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_52,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,(
    ! [A_12] : k2_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_26,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,(
    ! [A_12] : k1_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_380,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_399,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_380])).

tff(c_82,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_198,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_157,c_82])).

tff(c_408,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_198])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_159,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_86])).

tff(c_168,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_159])).

tff(c_432,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_168])).

tff(c_425,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_399])).

tff(c_431,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_169])).

tff(c_1307,plain,(
    ! [B_175,C_176,A_177] :
      ( k6_partfun1(B_175) = k5_relat_1(k2_funct_1(C_176),C_176)
      | k1_xboole_0 = B_175
      | ~ v2_funct_1(C_176)
      | k2_relset_1(A_177,B_175,C_176) != B_175
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_175)))
      | ~ v1_funct_2(C_176,A_177,B_175)
      | ~ v1_funct_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1316,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_431,c_1307])).

tff(c_1332,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_432,c_425,c_80,c_1316])).

tff(c_1337,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1332])).

tff(c_170,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_177,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_169,c_170])).

tff(c_259,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_266,plain,
    ( k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_259])).

tff(c_306,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_427,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_306])).

tff(c_1345,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_427])).

tff(c_1356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_1345])).

tff(c_1358,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1332])).

tff(c_1363,plain,(
    ! [A_178,C_179,B_180] :
      ( k6_partfun1(A_178) = k5_relat_1(C_179,k2_funct_1(C_179))
      | k1_xboole_0 = B_180
      | ~ v2_funct_1(C_179)
      | k2_relset_1(A_178,B_180,C_179) != B_180
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_180)))
      | ~ v1_funct_2(C_179,A_178,B_180)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1372,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_431,c_1363])).

tff(c_1388,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_432,c_425,c_80,c_1372])).

tff(c_1389,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_1358,c_1388])).

tff(c_42,plain,(
    ! [A_15] :
      ( k1_relat_1(k5_relat_1(A_15,k2_funct_1(A_15))) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1397,plain,
    ( k1_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_42])).

tff(c_1404,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_96,c_1397])).

tff(c_1416,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_432])).

tff(c_1417,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_431])).

tff(c_54,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r2_funct_2(A_27,B_28,C_29,C_29)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(D_30,A_27,B_28)
      | ~ v1_funct_1(D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1499,plain,(
    ! [C_29] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_29,C_29)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_29,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_29) ) ),
    inference(resolution,[status(thm)],[c_1417,c_54])).

tff(c_1636,plain,(
    ! [C_191] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_191,C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_191,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1416,c_1499])).

tff(c_1638,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1417,c_1636])).

tff(c_1656,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1416,c_1638])).

tff(c_44,plain,(
    ! [A_16] :
      ( k2_funct_1(k2_funct_1(A_16)) = A_16
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_903,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_funct_1(k2_funct_1(C_140))
      | k2_relset_1(A_141,B_142,C_140) != B_142
      | ~ v2_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_2(C_140,A_141,B_142)
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_913,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_431,c_903])).

tff(c_932,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_432,c_80,c_425,c_913])).

tff(c_1069,plain,(
    ! [C_154,B_155,A_156] :
      ( v1_funct_2(k2_funct_1(C_154),B_155,A_156)
      | k2_relset_1(A_156,B_155,C_154) != B_155
      | ~ v2_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155)))
      | ~ v1_funct_2(C_154,A_156,B_155)
      | ~ v1_funct_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1079,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_431,c_1069])).

tff(c_1098,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_432,c_80,c_425,c_1079])).

tff(c_1411,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1098])).

tff(c_30,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1413,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_425])).

tff(c_1264,plain,(
    ! [C_172,B_173,A_174] :
      ( m1_subset_1(k2_funct_1(C_172),k1_zfmisc_1(k2_zfmisc_1(B_173,A_174)))
      | k2_relset_1(A_174,B_173,C_172) != B_173
      | ~ v2_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173)))
      | ~ v1_funct_2(C_172,A_174,B_173)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4420,plain,(
    ! [C_346,A_347,B_348] :
      ( v1_relat_1(k2_funct_1(C_346))
      | k2_relset_1(A_347,B_348,C_346) != B_348
      | ~ v2_funct_1(C_346)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348)))
      | ~ v1_funct_2(C_346,A_347,B_348)
      | ~ v1_funct_1(C_346) ) ),
    inference(resolution,[status(thm)],[c_1264,c_46])).

tff(c_4434,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1417,c_4420])).

tff(c_4465,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1416,c_80,c_1413,c_4434])).

tff(c_1357,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1332])).

tff(c_649,plain,(
    ! [A_117] :
      ( k1_relat_1(k5_relat_1(A_117,k2_funct_1(A_117))) = k1_relat_1(A_117)
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6967,plain,(
    ! [A_418] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_418),A_418)) = k1_relat_1(k2_funct_1(A_418))
      | ~ v2_funct_1(k2_funct_1(A_418))
      | ~ v1_funct_1(k2_funct_1(A_418))
      | ~ v1_relat_1(k2_funct_1(A_418))
      | ~ v2_funct_1(A_418)
      | ~ v1_funct_1(A_418)
      | ~ v1_relat_1(A_418) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_649])).

tff(c_7006,plain,
    ( k1_relat_1(k6_partfun1(k2_relat_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_6967])).

tff(c_7013,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_4465,c_932,c_96,c_7006])).

tff(c_7014,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7013])).

tff(c_7017,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_7014])).

tff(c_7021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_7017])).

tff(c_7023,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7013])).

tff(c_7022,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7013])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_808,plain,(
    ! [B_134,A_135] :
      ( m1_subset_1(B_134,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_134),A_135)))
      | ~ r1_tarski(k2_relat_1(B_134),A_135)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1695,plain,(
    ! [B_195,A_196] :
      ( k2_relset_1(k1_relat_1(B_195),A_196,B_195) = k2_relat_1(B_195)
      | ~ r1_tarski(k2_relat_1(B_195),A_196)
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(resolution,[status(thm)],[c_808,c_50])).

tff(c_1719,plain,(
    ! [B_195] :
      ( k2_relset_1(k1_relat_1(B_195),k2_relat_1(B_195),B_195) = k2_relat_1(B_195)
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(resolution,[status(thm)],[c_8,c_1695])).

tff(c_7102,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7022,c_1719])).

tff(c_7137,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_932,c_7102])).

tff(c_7165,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7137])).

tff(c_7172,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_7165])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_839,plain,(
    ! [B_134,A_135] :
      ( r1_tarski(B_134,k2_zfmisc_1(k1_relat_1(B_134),A_135))
      | ~ r1_tarski(k2_relat_1(B_134),A_135)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_808,c_20])).

tff(c_7105,plain,(
    ! [A_135] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),A_135))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_135)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7022,c_839])).

tff(c_7139,plain,(
    ! [A_135] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),A_135))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4465,c_932,c_7105])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_477,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k2_relset_1(A_98,B_99,C_100),k1_zfmisc_1(B_99))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_739,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(k2_relset_1(A_127,B_128,C_129),B_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(resolution,[status(thm)],[c_477,c_20])).

tff(c_758,plain,(
    ! [A_127,B_128,A_7] :
      ( r1_tarski(k2_relset_1(A_127,B_128,A_7),B_128)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_127,B_128)) ) ),
    inference(resolution,[status(thm)],[c_22,c_739])).

tff(c_7180,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7172,c_758])).

tff(c_7601,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_7180])).

tff(c_7605,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7139,c_7601])).

tff(c_7609,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7605])).

tff(c_7612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_8,c_7609])).

tff(c_7614,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_7180])).

tff(c_933,plain,(
    ! [A_7,A_141,B_142] :
      ( v1_funct_1(k2_funct_1(A_7))
      | k2_relset_1(A_141,B_142,A_7) != B_142
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_2(A_7,A_141,B_142)
      | ~ v1_funct_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_141,B_142)) ) ),
    inference(resolution,[status(thm)],[c_22,c_903])).

tff(c_7635,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7614,c_933])).

tff(c_7646,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_1411,c_7023,c_7172,c_7635])).

tff(c_7652,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7646])).

tff(c_7655,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7652])).

tff(c_7659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_7655])).

tff(c_7661,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7646])).

tff(c_1168,plain,(
    ! [A_162,B_163,C_164] :
      ( k2_tops_2(A_162,B_163,C_164) = k2_funct_1(C_164)
      | ~ v2_funct_1(C_164)
      | k2_relset_1(A_162,B_163,C_164) != B_163
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_2(C_164,A_162,B_163)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_7662,plain,(
    ! [A_431,B_432,A_433] :
      ( k2_tops_2(A_431,B_432,A_433) = k2_funct_1(A_433)
      | ~ v2_funct_1(A_433)
      | k2_relset_1(A_431,B_432,A_433) != B_432
      | ~ v1_funct_2(A_433,A_431,B_432)
      | ~ v1_funct_1(A_433)
      | ~ r1_tarski(A_433,k2_zfmisc_1(A_431,B_432)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1168])).

tff(c_7665,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7614,c_7662])).

tff(c_7734,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_1411,c_7172,c_7023,c_7665])).

tff(c_8414,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7661,c_7734])).

tff(c_1178,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_431,c_1168])).

tff(c_1197,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_432,c_425,c_80,c_1178])).

tff(c_78,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_214,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_158,c_158,c_157,c_157,c_157,c_78])).

tff(c_428,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_408,c_408,c_214])).

tff(c_1201,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_428])).

tff(c_1409,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1404,c_1201])).

tff(c_8415,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8414,c_1409])).

tff(c_8422,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8415])).

tff(c_8425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_1656,c_8422])).

tff(c_8426,plain,(
    k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_8429,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8426,c_169])).

tff(c_8555,plain,(
    ! [A_469,B_470,C_471] :
      ( k2_relset_1(A_469,B_470,C_471) = k2_relat_1(C_471)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8582,plain,(
    ! [C_474] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_474) = k2_relat_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8426,c_8555])).

tff(c_8592,plain,
    ( k2_struct_0('#skF_2') = k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8582,c_198])).

tff(c_8608,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8429,c_8592])).

tff(c_8618,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_8608,c_198])).

tff(c_8620,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_168])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8616,plain,(
    k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_8426])).

tff(c_10009,plain,(
    ! [B_578,C_579,A_580] :
      ( k6_partfun1(B_578) = k5_relat_1(k2_funct_1(C_579),C_579)
      | k1_xboole_0 = B_578
      | ~ v2_funct_1(C_579)
      | k2_relset_1(A_580,B_578,C_579) != B_578
      | ~ m1_subset_1(C_579,k1_zfmisc_1(k2_zfmisc_1(A_580,B_578)))
      | ~ v1_funct_2(C_579,A_580,B_578)
      | ~ v1_funct_1(C_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10018,plain,(
    ! [C_579] :
      ( k5_relat_1(k2_funct_1(C_579),C_579) = k6_partfun1(k2_relat_1('#skF_3'))
      | k2_relat_1('#skF_3') = k1_xboole_0
      | ~ v2_funct_1(C_579)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_579) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_579,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_579,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_579) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8616,c_10009])).

tff(c_10257,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10018])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_180,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(u1_struct_0(A_59))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_186,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_180])).

tff(c_190,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_186])).

tff(c_191,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_190])).

tff(c_8619,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_191])).

tff(c_10283,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10257,c_8619])).

tff(c_10297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10283])).

tff(c_10299,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10018])).

tff(c_9884,plain,(
    ! [A_568,C_569,B_570] :
      ( k6_partfun1(A_568) = k5_relat_1(C_569,k2_funct_1(C_569))
      | k1_xboole_0 = B_570
      | ~ v2_funct_1(C_569)
      | k2_relset_1(A_568,B_570,C_569) != B_570
      | ~ m1_subset_1(C_569,k1_zfmisc_1(k2_zfmisc_1(A_568,B_570)))
      | ~ v1_funct_2(C_569,A_568,B_570)
      | ~ v1_funct_1(C_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_9893,plain,(
    ! [C_569] :
      ( k5_relat_1(C_569,k2_funct_1(C_569)) = k6_partfun1(k2_struct_0('#skF_1'))
      | k2_relat_1('#skF_3') = k1_xboole_0
      | ~ v2_funct_1(C_569)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_569) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_569,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_569,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8616,c_9884])).

tff(c_10518,plain,(
    ! [C_615] :
      ( k5_relat_1(C_615,k2_funct_1(C_615)) = k6_partfun1(k2_struct_0('#skF_1'))
      | ~ v2_funct_1(C_615)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_615) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_615,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_615,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_615) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10299,c_9893])).

tff(c_10523,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8620,c_10518])).

tff(c_10527,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8429,c_8618,c_80,c_10523])).

tff(c_40,plain,(
    ! [A_15] :
      ( k2_relat_1(k5_relat_1(A_15,k2_funct_1(A_15))) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10531,plain,
    ( k2_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10527,c_40])).

tff(c_10538,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_95,c_10531])).

tff(c_10554,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_8620])).

tff(c_10555,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_8616])).

tff(c_66,plain,(
    ! [B_38,A_37] :
      ( m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_38),A_37)))
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_10217,plain,(
    ! [A_590,B_591,C_592,D_593] :
      ( r2_funct_2(A_590,B_591,C_592,C_592)
      | ~ m1_subset_1(D_593,k1_zfmisc_1(k2_zfmisc_1(A_590,B_591)))
      | ~ v1_funct_2(D_593,A_590,B_591)
      | ~ v1_funct_1(D_593)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(A_590,B_591)))
      | ~ v1_funct_2(C_592,A_590,B_591)
      | ~ v1_funct_1(C_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_22044,plain,(
    ! [B_1015,A_1016,C_1017] :
      ( r2_funct_2(k1_relat_1(B_1015),A_1016,C_1017,C_1017)
      | ~ v1_funct_2(B_1015,k1_relat_1(B_1015),A_1016)
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1015),A_1016)))
      | ~ v1_funct_2(C_1017,k1_relat_1(B_1015),A_1016)
      | ~ v1_funct_1(C_1017)
      | ~ r1_tarski(k2_relat_1(B_1015),A_1016)
      | ~ v1_funct_1(B_1015)
      | ~ v1_relat_1(B_1015) ) ),
    inference(resolution,[status(thm)],[c_66,c_10217])).

tff(c_22061,plain,(
    ! [C_1017] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_1017,C_1017)
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_1017,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_1017)
      | ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10554,c_22044])).

tff(c_22097,plain,(
    ! [C_1021] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_1021,C_1021)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_1021,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_1021) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_8,c_10555,c_22061])).

tff(c_9107,plain,(
    ! [C_503,A_504,B_505] :
      ( v1_funct_1(k2_funct_1(C_503))
      | k2_relset_1(A_504,B_505,C_503) != B_505
      | ~ v2_funct_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_505)))
      | ~ v1_funct_2(C_503,A_504,B_505)
      | ~ v1_funct_1(C_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_9629,plain,(
    ! [C_544] :
      ( v1_funct_1(k2_funct_1(C_544))
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_544) != k2_relat_1('#skF_3')
      | ~ v2_funct_1(C_544)
      | ~ m1_subset_1(C_544,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_544,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8616,c_9107])).

tff(c_9632,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8620,c_9629])).

tff(c_9635,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8429,c_80,c_8618,c_9632])).

tff(c_10553,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_8618])).

tff(c_9736,plain,(
    ! [C_555,B_556,A_557] :
      ( m1_subset_1(k2_funct_1(C_555),k1_zfmisc_1(k2_zfmisc_1(B_556,A_557)))
      | k2_relset_1(A_557,B_556,C_555) != B_556
      | ~ v2_funct_1(C_555)
      | ~ m1_subset_1(C_555,k1_zfmisc_1(k2_zfmisc_1(A_557,B_556)))
      | ~ v1_funct_2(C_555,A_557,B_556)
      | ~ v1_funct_1(C_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12280,plain,(
    ! [C_705,A_706,B_707] :
      ( v1_relat_1(k2_funct_1(C_705))
      | k2_relset_1(A_706,B_707,C_705) != B_707
      | ~ v2_funct_1(C_705)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(A_706,B_707)))
      | ~ v1_funct_2(C_705,A_706,B_707)
      | ~ v1_funct_1(C_705) ) ),
    inference(resolution,[status(thm)],[c_9736,c_46])).

tff(c_13839,plain,(
    ! [C_785] :
      ( v1_relat_1(k2_funct_1(C_785))
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_785) != k2_relat_1('#skF_3')
      | ~ v2_funct_1(C_785)
      | ~ m1_subset_1(C_785,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_785,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_785) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10555,c_12280])).

tff(c_13846,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10554,c_13839])).

tff(c_13858,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8429,c_80,c_10553,c_13846])).

tff(c_10298,plain,(
    ! [C_579] :
      ( k5_relat_1(k2_funct_1(C_579),C_579) = k6_partfun1(k2_relat_1('#skF_3'))
      | ~ v2_funct_1(C_579)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_579) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_579,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_579,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_579) ) ),
    inference(splitRight,[status(thm)],[c_10018])).

tff(c_14240,plain,(
    ! [C_794] :
      ( k5_relat_1(k2_funct_1(C_794),C_794) = k6_partfun1(k2_relat_1('#skF_3'))
      | ~ v2_funct_1(C_794)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_794) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_794,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_794,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_794) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_10538,c_10298])).

tff(c_14245,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10554,c_14240])).

tff(c_14255,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8429,c_10553,c_80,c_14245])).

tff(c_8754,plain,(
    ! [A_489] :
      ( k2_relat_1(k5_relat_1(A_489,k2_funct_1(A_489))) = k1_relat_1(A_489)
      | ~ v2_funct_1(A_489)
      | ~ v1_funct_1(A_489)
      | ~ v1_relat_1(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14316,plain,(
    ! [A_797] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_797),A_797)) = k1_relat_1(k2_funct_1(A_797))
      | ~ v2_funct_1(k2_funct_1(A_797))
      | ~ v1_funct_1(k2_funct_1(A_797))
      | ~ v1_relat_1(k2_funct_1(A_797))
      | ~ v2_funct_1(A_797)
      | ~ v1_funct_1(A_797)
      | ~ v1_relat_1(A_797) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8754])).

tff(c_14362,plain,
    ( k2_relat_1(k6_partfun1(k2_relat_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14255,c_14316])).

tff(c_14369,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_13858,c_9635,c_95,c_14362])).

tff(c_14370,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14369])).

tff(c_14373,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_14370])).

tff(c_14377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_14373])).

tff(c_14378,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_14369])).

tff(c_8977,plain,(
    ! [B_498,A_499] :
      ( m1_subset_1(B_498,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_498),A_499)))
      | ~ r1_tarski(k2_relat_1(B_498),A_499)
      | ~ v1_funct_1(B_498)
      | ~ v1_relat_1(B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_9005,plain,(
    ! [B_498,A_499] :
      ( r1_tarski(B_498,k2_zfmisc_1(k1_relat_1(B_498),A_499))
      | ~ r1_tarski(k2_relat_1(B_498),A_499)
      | ~ v1_funct_1(B_498)
      | ~ v1_relat_1(B_498) ) ),
    inference(resolution,[status(thm)],[c_8977,c_20])).

tff(c_14408,plain,(
    ! [A_499] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),A_499))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_499)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14378,c_9005])).

tff(c_14438,plain,(
    ! [A_499] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),A_499))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_499) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13858,c_9635,c_14408])).

tff(c_10572,plain,(
    ! [B_616,A_617] :
      ( k2_relset_1(k1_relat_1(B_616),A_617,B_616) = k2_relat_1(B_616)
      | ~ r1_tarski(k2_relat_1(B_616),A_617)
      | ~ v1_funct_1(B_616)
      | ~ v1_relat_1(B_616) ) ),
    inference(resolution,[status(thm)],[c_8977,c_50])).

tff(c_10605,plain,(
    ! [B_616] :
      ( k2_relset_1(k1_relat_1(B_616),k2_relat_1(B_616),B_616) = k2_relat_1(B_616)
      | ~ v1_funct_1(B_616)
      | ~ v1_relat_1(B_616) ) ),
    inference(resolution,[status(thm)],[c_8,c_10572])).

tff(c_14402,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14378,c_10605])).

tff(c_14434,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13858,c_9635,c_14402])).

tff(c_14464,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_14434])).

tff(c_14471,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_14464])).

tff(c_8879,plain,(
    ! [A_494,B_495,C_496] :
      ( m1_subset_1(k2_relset_1(A_494,B_495,C_496),k1_zfmisc_1(B_495))
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_494,B_495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9278,plain,(
    ! [A_521,B_522,C_523] :
      ( r1_tarski(k2_relset_1(A_521,B_522,C_523),B_522)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(resolution,[status(thm)],[c_8879,c_20])).

tff(c_9298,plain,(
    ! [A_521,B_522,A_7] :
      ( r1_tarski(k2_relset_1(A_521,B_522,A_7),B_522)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_521,B_522)) ) ),
    inference(resolution,[status(thm)],[c_22,c_9278])).

tff(c_14479,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14471,c_9298])).

tff(c_14957,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_14479])).

tff(c_15008,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14438,c_14957])).

tff(c_15011,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15008])).

tff(c_15014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_8,c_15011])).

tff(c_15015,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14479])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15032,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_15015,c_4])).

tff(c_15084,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_15032])).

tff(c_15087,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15084])).

tff(c_15090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_8,c_15087])).

tff(c_15091,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15032])).

tff(c_68,plain,(
    ! [B_38,A_37] :
      ( v1_funct_2(B_38,k1_relat_1(B_38),A_37)
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_14414,plain,(
    ! [A_37] :
      ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),A_37)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_37)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14378,c_68])).

tff(c_14442,plain,(
    ! [A_37] :
      ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),A_37)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13858,c_9635,c_14414])).

tff(c_15101,plain,(
    ! [A_37] :
      ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),A_37)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15091,c_14442])).

tff(c_14379,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14369])).

tff(c_15102,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15091,c_14471])).

tff(c_15250,plain,(
    ! [A_814] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),A_814))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_814) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15091,c_14438])).

tff(c_10063,plain,(
    ! [C_583] :
      ( m1_subset_1(k2_funct_1(C_583),k1_zfmisc_1('#skF_3'))
      | k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),C_583) != k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_583)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_583,k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8616,c_9736])).

tff(c_10083,plain,(
    ! [A_7] :
      ( m1_subset_1(k2_funct_1(A_7),k1_zfmisc_1('#skF_3'))
      | k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),A_7) != k2_struct_0('#skF_1')
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_2(A_7,k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_10063])).

tff(c_14742,plain,(
    ! [A_7] :
      ( m1_subset_1(k2_funct_1(A_7),k1_zfmisc_1('#skF_3'))
      | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),A_7) != k1_relat_1('#skF_3')
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_2(A_7,k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_10538,c_10538,c_10538,c_10083])).

tff(c_15254,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15250,c_14742])).

tff(c_15280,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9635,c_14379,c_15102,c_15254])).

tff(c_15660,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15280])).

tff(c_15663,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15101,c_15660])).

tff(c_15676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15663])).

tff(c_15678,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15280])).

tff(c_15677,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15280])).

tff(c_15692,plain,(
    r1_tarski(k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_15677,c_20])).

tff(c_15761,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_15692,c_4])).

tff(c_16039,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_15761])).

tff(c_16042,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_16039])).

tff(c_16045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_88,c_80,c_8,c_16042])).

tff(c_16046,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15761])).

tff(c_14411,plain,(
    ! [A_37] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),A_37)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_37)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14378,c_66])).

tff(c_14440,plain,(
    ! [A_37] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),A_37)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13858,c_9635,c_14411])).

tff(c_15097,plain,(
    ! [A_37] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),A_37)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15091,c_14440])).

tff(c_48,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k2_relset_1(A_20,B_21,C_22),k1_zfmisc_1(B_21))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15233,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(k1_relat_1('#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_15102,c_48])).

tff(c_16297,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_15233])).

tff(c_16300,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15097,c_16297])).

tff(c_16310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16300])).

tff(c_16312,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_15233])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_tops_2(A_41,B_42,C_43) = k2_funct_1(C_43)
      | ~ v2_funct_1(C_43)
      | k2_relset_1(A_41,B_42,C_43) != B_42
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_2(C_43,A_41,B_42)
      | ~ v1_funct_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_16363,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16312,c_76])).

tff(c_16400,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9635,c_15678,c_15102,c_14379,c_16046,c_16363])).

tff(c_9447,plain,(
    ! [A_533,B_534,C_535] :
      ( k2_tops_2(A_533,B_534,C_535) = k2_funct_1(C_535)
      | ~ v2_funct_1(C_535)
      | k2_relset_1(A_533,B_534,C_535) != B_534
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534)))
      | ~ v1_funct_2(C_535,A_533,B_534)
      | ~ v1_funct_1(C_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_9969,plain,(
    ! [C_575] :
      ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_575) = k2_funct_1(C_575)
      | ~ v2_funct_1(C_575)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_575) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_575,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_575,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_575) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8616,c_9447])).

tff(c_9972,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8620,c_9969])).

tff(c_9975,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8429,c_8618,c_80,c_9972])).

tff(c_8617,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8608,c_8608,c_8608,c_214])).

tff(c_9976,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9975,c_8617])).

tff(c_10545,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10538,c_10538,c_9976])).

tff(c_16416,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16400,c_10545])).

tff(c_22100,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22097,c_16416])).

tff(c_22104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10554,c_8429,c_22100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.70/4.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.70/4.77  
% 11.70/4.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.70/4.77  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.70/4.77  
% 11.70/4.77  %Foreground sorts:
% 11.70/4.77  
% 11.70/4.77  
% 11.70/4.77  %Background operators:
% 11.70/4.77  
% 11.70/4.77  
% 11.70/4.77  %Foreground operators:
% 11.70/4.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.70/4.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.70/4.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.70/4.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.70/4.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.70/4.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.70/4.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.70/4.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.70/4.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.70/4.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.70/4.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.70/4.77  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 11.70/4.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.70/4.77  tff('#skF_2', type, '#skF_2': $i).
% 11.70/4.77  tff('#skF_3', type, '#skF_3': $i).
% 11.70/4.77  tff('#skF_1', type, '#skF_1': $i).
% 11.70/4.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.70/4.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.70/4.77  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.70/4.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.70/4.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.70/4.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.70/4.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.70/4.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.70/4.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.70/4.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.70/4.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.70/4.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.70/4.77  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 11.70/4.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.70/4.77  
% 11.70/4.81  tff(f_214, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 11.70/4.81  tff(f_172, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 11.70/4.81  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.70/4.81  tff(f_110, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.70/4.81  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.70/4.81  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.70/4.81  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.70/4.81  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.70/4.81  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 11.70/4.81  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.70/4.81  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.70/4.81  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 11.70/4.81  tff(f_124, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 11.70/4.81  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 11.70/4.81  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.70/4.81  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.70/4.81  tff(f_68, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 11.70/4.81  tff(f_168, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 11.70/4.81  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 11.70/4.81  tff(f_192, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 11.70/4.81  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.70/4.81  tff(f_180, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.70/4.81  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_94, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_150, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_172])).
% 11.70/4.81  tff(c_158, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_94, c_150])).
% 11.70/4.81  tff(c_90, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_157, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_150])).
% 11.70/4.81  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_169, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_157, c_84])).
% 11.70/4.81  tff(c_215, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.70/4.81  tff(c_232, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_169, c_215])).
% 11.70/4.81  tff(c_80, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_52, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.70/4.81  tff(c_28, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.70/4.81  tff(c_95, plain, (![A_12]: (k2_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 11.70/4.81  tff(c_26, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.70/4.81  tff(c_96, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_26])).
% 11.70/4.81  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.70/4.81  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.70/4.81  tff(c_380, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.70/4.81  tff(c_399, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_169, c_380])).
% 11.70/4.81  tff(c_82, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_198, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_157, c_82])).
% 11.70/4.81  tff(c_408, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_198])).
% 11.70/4.81  tff(c_86, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_159, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_86])).
% 11.70/4.81  tff(c_168, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_159])).
% 11.70/4.81  tff(c_432, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_168])).
% 11.70/4.81  tff(c_425, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_399])).
% 11.70/4.81  tff(c_431, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_169])).
% 11.70/4.81  tff(c_1307, plain, (![B_175, C_176, A_177]: (k6_partfun1(B_175)=k5_relat_1(k2_funct_1(C_176), C_176) | k1_xboole_0=B_175 | ~v2_funct_1(C_176) | k2_relset_1(A_177, B_175, C_176)!=B_175 | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_175))) | ~v1_funct_2(C_176, A_177, B_175) | ~v1_funct_1(C_176))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.70/4.81  tff(c_1316, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_431, c_1307])).
% 11.70/4.81  tff(c_1332, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_432, c_425, c_80, c_1316])).
% 11.70/4.81  tff(c_1337, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1332])).
% 11.70/4.81  tff(c_170, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.70/4.81  tff(c_177, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_169, c_170])).
% 11.70/4.81  tff(c_259, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.70/4.81  tff(c_266, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))='#skF_3' | ~r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')), '#skF_3')), inference(resolution, [status(thm)], [c_177, c_259])).
% 11.70/4.81  tff(c_306, plain, (~r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_266])).
% 11.70/4.81  tff(c_427, plain, (~r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_306])).
% 11.70/4.81  tff(c_1345, plain, (~r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_427])).
% 11.70/4.81  tff(c_1356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_1345])).
% 11.70/4.81  tff(c_1358, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1332])).
% 11.70/4.81  tff(c_1363, plain, (![A_178, C_179, B_180]: (k6_partfun1(A_178)=k5_relat_1(C_179, k2_funct_1(C_179)) | k1_xboole_0=B_180 | ~v2_funct_1(C_179) | k2_relset_1(A_178, B_180, C_179)!=B_180 | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_180))) | ~v1_funct_2(C_179, A_178, B_180) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.70/4.81  tff(c_1372, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_431, c_1363])).
% 11.70/4.81  tff(c_1388, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_432, c_425, c_80, c_1372])).
% 11.70/4.81  tff(c_1389, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_1358, c_1388])).
% 11.70/4.81  tff(c_42, plain, (![A_15]: (k1_relat_1(k5_relat_1(A_15, k2_funct_1(A_15)))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.70/4.81  tff(c_1397, plain, (k1_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1389, c_42])).
% 11.70/4.81  tff(c_1404, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_96, c_1397])).
% 11.70/4.81  tff(c_1416, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_432])).
% 11.70/4.81  tff(c_1417, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_431])).
% 11.70/4.81  tff(c_54, plain, (![A_27, B_28, C_29, D_30]: (r2_funct_2(A_27, B_28, C_29, C_29) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(D_30, A_27, B_28) | ~v1_funct_1(D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.70/4.81  tff(c_1499, plain, (![C_29]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_29, C_29) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_29, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_29))), inference(resolution, [status(thm)], [c_1417, c_54])).
% 11.70/4.81  tff(c_1636, plain, (![C_191]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_191, C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_191, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_191))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1416, c_1499])).
% 11.70/4.81  tff(c_1638, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1417, c_1636])).
% 11.70/4.81  tff(c_1656, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1416, c_1638])).
% 11.70/4.81  tff(c_44, plain, (![A_16]: (k2_funct_1(k2_funct_1(A_16))=A_16 | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.70/4.81  tff(c_36, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.70/4.81  tff(c_903, plain, (![C_140, A_141, B_142]: (v1_funct_1(k2_funct_1(C_140)) | k2_relset_1(A_141, B_142, C_140)!=B_142 | ~v2_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_2(C_140, A_141, B_142) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.70/4.81  tff(c_913, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_431, c_903])).
% 11.70/4.81  tff(c_932, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_432, c_80, c_425, c_913])).
% 11.70/4.81  tff(c_1069, plain, (![C_154, B_155, A_156]: (v1_funct_2(k2_funct_1(C_154), B_155, A_156) | k2_relset_1(A_156, B_155, C_154)!=B_155 | ~v2_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))) | ~v1_funct_2(C_154, A_156, B_155) | ~v1_funct_1(C_154))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.70/4.81  tff(c_1079, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_431, c_1069])).
% 11.70/4.81  tff(c_1098, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_432, c_80, c_425, c_1079])).
% 11.70/4.81  tff(c_1411, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1098])).
% 11.70/4.81  tff(c_30, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.70/4.81  tff(c_1413, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_425])).
% 11.70/4.81  tff(c_1264, plain, (![C_172, B_173, A_174]: (m1_subset_1(k2_funct_1(C_172), k1_zfmisc_1(k2_zfmisc_1(B_173, A_174))) | k2_relset_1(A_174, B_173, C_172)!=B_173 | ~v2_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))) | ~v1_funct_2(C_172, A_174, B_173) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.70/4.81  tff(c_46, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.70/4.81  tff(c_4420, plain, (![C_346, A_347, B_348]: (v1_relat_1(k2_funct_1(C_346)) | k2_relset_1(A_347, B_348, C_346)!=B_348 | ~v2_funct_1(C_346) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))) | ~v1_funct_2(C_346, A_347, B_348) | ~v1_funct_1(C_346))), inference(resolution, [status(thm)], [c_1264, c_46])).
% 11.70/4.81  tff(c_4434, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1417, c_4420])).
% 11.70/4.81  tff(c_4465, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1416, c_80, c_1413, c_4434])).
% 11.70/4.81  tff(c_1357, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1332])).
% 11.70/4.81  tff(c_649, plain, (![A_117]: (k1_relat_1(k5_relat_1(A_117, k2_funct_1(A_117)))=k1_relat_1(A_117) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.70/4.81  tff(c_6967, plain, (![A_418]: (k1_relat_1(k5_relat_1(k2_funct_1(A_418), A_418))=k1_relat_1(k2_funct_1(A_418)) | ~v2_funct_1(k2_funct_1(A_418)) | ~v1_funct_1(k2_funct_1(A_418)) | ~v1_relat_1(k2_funct_1(A_418)) | ~v2_funct_1(A_418) | ~v1_funct_1(A_418) | ~v1_relat_1(A_418))), inference(superposition, [status(thm), theory('equality')], [c_44, c_649])).
% 11.70/4.81  tff(c_7006, plain, (k1_relat_1(k6_partfun1(k2_relat_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1357, c_6967])).
% 11.70/4.81  tff(c_7013, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_4465, c_932, c_96, c_7006])).
% 11.70/4.81  tff(c_7014, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7013])).
% 11.70/4.81  tff(c_7017, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_7014])).
% 11.70/4.81  tff(c_7021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_7017])).
% 11.70/4.81  tff(c_7023, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7013])).
% 11.70/4.81  tff(c_7022, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_7013])).
% 11.70/4.81  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.70/4.81  tff(c_808, plain, (![B_134, A_135]: (m1_subset_1(B_134, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_134), A_135))) | ~r1_tarski(k2_relat_1(B_134), A_135) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.70/4.81  tff(c_50, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.70/4.81  tff(c_1695, plain, (![B_195, A_196]: (k2_relset_1(k1_relat_1(B_195), A_196, B_195)=k2_relat_1(B_195) | ~r1_tarski(k2_relat_1(B_195), A_196) | ~v1_funct_1(B_195) | ~v1_relat_1(B_195))), inference(resolution, [status(thm)], [c_808, c_50])).
% 11.70/4.81  tff(c_1719, plain, (![B_195]: (k2_relset_1(k1_relat_1(B_195), k2_relat_1(B_195), B_195)=k2_relat_1(B_195) | ~v1_funct_1(B_195) | ~v1_relat_1(B_195))), inference(resolution, [status(thm)], [c_8, c_1695])).
% 11.70/4.81  tff(c_7102, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7022, c_1719])).
% 11.70/4.81  tff(c_7137, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_932, c_7102])).
% 11.70/4.81  tff(c_7165, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_7137])).
% 11.70/4.81  tff(c_7172, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_7165])).
% 11.70/4.81  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.70/4.81  tff(c_839, plain, (![B_134, A_135]: (r1_tarski(B_134, k2_zfmisc_1(k1_relat_1(B_134), A_135)) | ~r1_tarski(k2_relat_1(B_134), A_135) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_808, c_20])).
% 11.70/4.81  tff(c_7105, plain, (![A_135]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), A_135)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_135) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7022, c_839])).
% 11.70/4.81  tff(c_7139, plain, (![A_135]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), A_135)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_135))), inference(demodulation, [status(thm), theory('equality')], [c_4465, c_932, c_7105])).
% 11.70/4.81  tff(c_22, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.70/4.81  tff(c_477, plain, (![A_98, B_99, C_100]: (m1_subset_1(k2_relset_1(A_98, B_99, C_100), k1_zfmisc_1(B_99)) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.70/4.81  tff(c_739, plain, (![A_127, B_128, C_129]: (r1_tarski(k2_relset_1(A_127, B_128, C_129), B_128) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(resolution, [status(thm)], [c_477, c_20])).
% 11.70/4.81  tff(c_758, plain, (![A_127, B_128, A_7]: (r1_tarski(k2_relset_1(A_127, B_128, A_7), B_128) | ~r1_tarski(A_7, k2_zfmisc_1(A_127, B_128)))), inference(resolution, [status(thm)], [c_22, c_739])).
% 11.70/4.81  tff(c_7180, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7172, c_758])).
% 11.70/4.81  tff(c_7601, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_7180])).
% 11.70/4.81  tff(c_7605, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_7139, c_7601])).
% 11.70/4.81  tff(c_7609, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_7605])).
% 11.70/4.81  tff(c_7612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_8, c_7609])).
% 11.70/4.81  tff(c_7614, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_7180])).
% 11.70/4.81  tff(c_933, plain, (![A_7, A_141, B_142]: (v1_funct_1(k2_funct_1(A_7)) | k2_relset_1(A_141, B_142, A_7)!=B_142 | ~v2_funct_1(A_7) | ~v1_funct_2(A_7, A_141, B_142) | ~v1_funct_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_141, B_142)))), inference(resolution, [status(thm)], [c_22, c_903])).
% 11.70/4.81  tff(c_7635, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7614, c_933])).
% 11.70/4.81  tff(c_7646, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_932, c_1411, c_7023, c_7172, c_7635])).
% 11.70/4.81  tff(c_7652, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_7646])).
% 11.70/4.81  tff(c_7655, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_7652])).
% 11.70/4.81  tff(c_7659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_7655])).
% 11.70/4.81  tff(c_7661, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_7646])).
% 11.70/4.81  tff(c_1168, plain, (![A_162, B_163, C_164]: (k2_tops_2(A_162, B_163, C_164)=k2_funct_1(C_164) | ~v2_funct_1(C_164) | k2_relset_1(A_162, B_163, C_164)!=B_163 | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_2(C_164, A_162, B_163) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_192])).
% 11.70/4.81  tff(c_7662, plain, (![A_431, B_432, A_433]: (k2_tops_2(A_431, B_432, A_433)=k2_funct_1(A_433) | ~v2_funct_1(A_433) | k2_relset_1(A_431, B_432, A_433)!=B_432 | ~v1_funct_2(A_433, A_431, B_432) | ~v1_funct_1(A_433) | ~r1_tarski(A_433, k2_zfmisc_1(A_431, B_432)))), inference(resolution, [status(thm)], [c_22, c_1168])).
% 11.70/4.81  tff(c_7665, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7614, c_7662])).
% 11.70/4.81  tff(c_7734, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_932, c_1411, c_7172, c_7023, c_7665])).
% 11.70/4.81  tff(c_8414, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7661, c_7734])).
% 11.70/4.81  tff(c_1178, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_431, c_1168])).
% 11.70/4.81  tff(c_1197, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_432, c_425, c_80, c_1178])).
% 11.70/4.81  tff(c_78, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_214, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_158, c_158, c_157, c_157, c_157, c_78])).
% 11.70/4.81  tff(c_428, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_408, c_408, c_214])).
% 11.70/4.81  tff(c_1201, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_428])).
% 11.70/4.81  tff(c_1409, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1404, c_1201])).
% 11.70/4.81  tff(c_8415, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8414, c_1409])).
% 11.70/4.81  tff(c_8422, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_8415])).
% 11.70/4.81  tff(c_8425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_1656, c_8422])).
% 11.70/4.81  tff(c_8426, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))='#skF_3'), inference(splitRight, [status(thm)], [c_266])).
% 11.70/4.81  tff(c_8429, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8426, c_169])).
% 11.70/4.81  tff(c_8555, plain, (![A_469, B_470, C_471]: (k2_relset_1(A_469, B_470, C_471)=k2_relat_1(C_471) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.70/4.81  tff(c_8582, plain, (![C_474]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_474)=k2_relat_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8426, c_8555])).
% 11.70/4.81  tff(c_8592, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8582, c_198])).
% 11.70/4.81  tff(c_8608, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8429, c_8592])).
% 11.70/4.81  tff(c_8618, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8608, c_8608, c_198])).
% 11.70/4.81  tff(c_8620, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8608, c_168])).
% 11.70/4.81  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.70/4.81  tff(c_8616, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8608, c_8426])).
% 11.70/4.81  tff(c_10009, plain, (![B_578, C_579, A_580]: (k6_partfun1(B_578)=k5_relat_1(k2_funct_1(C_579), C_579) | k1_xboole_0=B_578 | ~v2_funct_1(C_579) | k2_relset_1(A_580, B_578, C_579)!=B_578 | ~m1_subset_1(C_579, k1_zfmisc_1(k2_zfmisc_1(A_580, B_578))) | ~v1_funct_2(C_579, A_580, B_578) | ~v1_funct_1(C_579))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.70/4.81  tff(c_10018, plain, (![C_579]: (k5_relat_1(k2_funct_1(C_579), C_579)=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1(C_579) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_579)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_579, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_579, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_579))), inference(superposition, [status(thm), theory('equality')], [c_8616, c_10009])).
% 11.70/4.81  tff(c_10257, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10018])).
% 11.70/4.81  tff(c_92, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 11.70/4.81  tff(c_180, plain, (![A_59]: (~v1_xboole_0(u1_struct_0(A_59)) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_180])).
% 11.70/4.81  tff(c_186, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_157, c_180])).
% 11.70/4.81  tff(c_190, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_186])).
% 11.70/4.81  tff(c_191, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_92, c_190])).
% 11.70/4.81  tff(c_8619, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8608, c_191])).
% 11.70/4.81  tff(c_10283, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10257, c_8619])).
% 11.70/4.81  tff(c_10297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_10283])).
% 11.70/4.81  tff(c_10299, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_10018])).
% 11.70/4.81  tff(c_9884, plain, (![A_568, C_569, B_570]: (k6_partfun1(A_568)=k5_relat_1(C_569, k2_funct_1(C_569)) | k1_xboole_0=B_570 | ~v2_funct_1(C_569) | k2_relset_1(A_568, B_570, C_569)!=B_570 | ~m1_subset_1(C_569, k1_zfmisc_1(k2_zfmisc_1(A_568, B_570))) | ~v1_funct_2(C_569, A_568, B_570) | ~v1_funct_1(C_569))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.70/4.81  tff(c_9893, plain, (![C_569]: (k5_relat_1(C_569, k2_funct_1(C_569))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1(C_569) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_569)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_569, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_569, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_569))), inference(superposition, [status(thm), theory('equality')], [c_8616, c_9884])).
% 11.70/4.81  tff(c_10518, plain, (![C_615]: (k5_relat_1(C_615, k2_funct_1(C_615))=k6_partfun1(k2_struct_0('#skF_1')) | ~v2_funct_1(C_615) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_615)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_615, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_615, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_615))), inference(negUnitSimplification, [status(thm)], [c_10299, c_9893])).
% 11.70/4.81  tff(c_10523, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8620, c_10518])).
% 11.70/4.81  tff(c_10527, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8429, c_8618, c_80, c_10523])).
% 11.70/4.81  tff(c_40, plain, (![A_15]: (k2_relat_1(k5_relat_1(A_15, k2_funct_1(A_15)))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.70/4.81  tff(c_10531, plain, (k2_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10527, c_40])).
% 11.70/4.81  tff(c_10538, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_95, c_10531])).
% 11.70/4.81  tff(c_10554, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10538, c_8620])).
% 11.70/4.81  tff(c_10555, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10538, c_8616])).
% 11.70/4.81  tff(c_66, plain, (![B_38, A_37]: (m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_38), A_37))) | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.70/4.81  tff(c_10217, plain, (![A_590, B_591, C_592, D_593]: (r2_funct_2(A_590, B_591, C_592, C_592) | ~m1_subset_1(D_593, k1_zfmisc_1(k2_zfmisc_1(A_590, B_591))) | ~v1_funct_2(D_593, A_590, B_591) | ~v1_funct_1(D_593) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(A_590, B_591))) | ~v1_funct_2(C_592, A_590, B_591) | ~v1_funct_1(C_592))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.70/4.81  tff(c_22044, plain, (![B_1015, A_1016, C_1017]: (r2_funct_2(k1_relat_1(B_1015), A_1016, C_1017, C_1017) | ~v1_funct_2(B_1015, k1_relat_1(B_1015), A_1016) | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1015), A_1016))) | ~v1_funct_2(C_1017, k1_relat_1(B_1015), A_1016) | ~v1_funct_1(C_1017) | ~r1_tarski(k2_relat_1(B_1015), A_1016) | ~v1_funct_1(B_1015) | ~v1_relat_1(B_1015))), inference(resolution, [status(thm)], [c_66, c_10217])).
% 11.70/4.81  tff(c_22061, plain, (![C_1017]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_1017, C_1017) | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_1017, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_1017) | ~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10554, c_22044])).
% 11.70/4.81  tff(c_22097, plain, (![C_1021]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_1021, C_1021) | ~m1_subset_1(C_1021, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_1021, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_1021))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_8, c_10555, c_22061])).
% 11.70/4.81  tff(c_9107, plain, (![C_503, A_504, B_505]: (v1_funct_1(k2_funct_1(C_503)) | k2_relset_1(A_504, B_505, C_503)!=B_505 | ~v2_funct_1(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_505))) | ~v1_funct_2(C_503, A_504, B_505) | ~v1_funct_1(C_503))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.70/4.81  tff(c_9629, plain, (![C_544]: (v1_funct_1(k2_funct_1(C_544)) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_544)!=k2_relat_1('#skF_3') | ~v2_funct_1(C_544) | ~m1_subset_1(C_544, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_544, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_544))), inference(superposition, [status(thm), theory('equality')], [c_8616, c_9107])).
% 11.70/4.81  tff(c_9632, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8620, c_9629])).
% 11.70/4.81  tff(c_9635, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8429, c_80, c_8618, c_9632])).
% 11.70/4.81  tff(c_10553, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10538, c_8618])).
% 11.70/4.81  tff(c_9736, plain, (![C_555, B_556, A_557]: (m1_subset_1(k2_funct_1(C_555), k1_zfmisc_1(k2_zfmisc_1(B_556, A_557))) | k2_relset_1(A_557, B_556, C_555)!=B_556 | ~v2_funct_1(C_555) | ~m1_subset_1(C_555, k1_zfmisc_1(k2_zfmisc_1(A_557, B_556))) | ~v1_funct_2(C_555, A_557, B_556) | ~v1_funct_1(C_555))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.70/4.81  tff(c_12280, plain, (![C_705, A_706, B_707]: (v1_relat_1(k2_funct_1(C_705)) | k2_relset_1(A_706, B_707, C_705)!=B_707 | ~v2_funct_1(C_705) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(A_706, B_707))) | ~v1_funct_2(C_705, A_706, B_707) | ~v1_funct_1(C_705))), inference(resolution, [status(thm)], [c_9736, c_46])).
% 11.70/4.81  tff(c_13839, plain, (![C_785]: (v1_relat_1(k2_funct_1(C_785)) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_785)!=k2_relat_1('#skF_3') | ~v2_funct_1(C_785) | ~m1_subset_1(C_785, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_785, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_785))), inference(superposition, [status(thm), theory('equality')], [c_10555, c_12280])).
% 11.70/4.81  tff(c_13846, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10554, c_13839])).
% 11.70/4.81  tff(c_13858, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8429, c_80, c_10553, c_13846])).
% 11.70/4.81  tff(c_10298, plain, (![C_579]: (k5_relat_1(k2_funct_1(C_579), C_579)=k6_partfun1(k2_relat_1('#skF_3')) | ~v2_funct_1(C_579) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_579)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_579, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_579, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_579))), inference(splitRight, [status(thm)], [c_10018])).
% 11.70/4.81  tff(c_14240, plain, (![C_794]: (k5_relat_1(k2_funct_1(C_794), C_794)=k6_partfun1(k2_relat_1('#skF_3')) | ~v2_funct_1(C_794) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_794)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_794, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_794, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_794))), inference(demodulation, [status(thm), theory('equality')], [c_10538, c_10538, c_10298])).
% 11.70/4.81  tff(c_14245, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10554, c_14240])).
% 11.70/4.81  tff(c_14255, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8429, c_10553, c_80, c_14245])).
% 11.70/4.81  tff(c_8754, plain, (![A_489]: (k2_relat_1(k5_relat_1(A_489, k2_funct_1(A_489)))=k1_relat_1(A_489) | ~v2_funct_1(A_489) | ~v1_funct_1(A_489) | ~v1_relat_1(A_489))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.70/4.81  tff(c_14316, plain, (![A_797]: (k2_relat_1(k5_relat_1(k2_funct_1(A_797), A_797))=k1_relat_1(k2_funct_1(A_797)) | ~v2_funct_1(k2_funct_1(A_797)) | ~v1_funct_1(k2_funct_1(A_797)) | ~v1_relat_1(k2_funct_1(A_797)) | ~v2_funct_1(A_797) | ~v1_funct_1(A_797) | ~v1_relat_1(A_797))), inference(superposition, [status(thm), theory('equality')], [c_44, c_8754])).
% 11.70/4.81  tff(c_14362, plain, (k2_relat_1(k6_partfun1(k2_relat_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14255, c_14316])).
% 11.70/4.81  tff(c_14369, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_13858, c_9635, c_95, c_14362])).
% 11.70/4.81  tff(c_14370, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14369])).
% 11.70/4.81  tff(c_14373, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_14370])).
% 11.70/4.81  tff(c_14377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_14373])).
% 11.70/4.81  tff(c_14378, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_14369])).
% 11.70/4.81  tff(c_8977, plain, (![B_498, A_499]: (m1_subset_1(B_498, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_498), A_499))) | ~r1_tarski(k2_relat_1(B_498), A_499) | ~v1_funct_1(B_498) | ~v1_relat_1(B_498))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.70/4.81  tff(c_9005, plain, (![B_498, A_499]: (r1_tarski(B_498, k2_zfmisc_1(k1_relat_1(B_498), A_499)) | ~r1_tarski(k2_relat_1(B_498), A_499) | ~v1_funct_1(B_498) | ~v1_relat_1(B_498))), inference(resolution, [status(thm)], [c_8977, c_20])).
% 11.70/4.81  tff(c_14408, plain, (![A_499]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), A_499)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_499) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14378, c_9005])).
% 11.70/4.81  tff(c_14438, plain, (![A_499]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), A_499)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_499))), inference(demodulation, [status(thm), theory('equality')], [c_13858, c_9635, c_14408])).
% 11.70/4.81  tff(c_10572, plain, (![B_616, A_617]: (k2_relset_1(k1_relat_1(B_616), A_617, B_616)=k2_relat_1(B_616) | ~r1_tarski(k2_relat_1(B_616), A_617) | ~v1_funct_1(B_616) | ~v1_relat_1(B_616))), inference(resolution, [status(thm)], [c_8977, c_50])).
% 11.70/4.81  tff(c_10605, plain, (![B_616]: (k2_relset_1(k1_relat_1(B_616), k2_relat_1(B_616), B_616)=k2_relat_1(B_616) | ~v1_funct_1(B_616) | ~v1_relat_1(B_616))), inference(resolution, [status(thm)], [c_8, c_10572])).
% 11.70/4.81  tff(c_14402, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14378, c_10605])).
% 11.70/4.81  tff(c_14434, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13858, c_9635, c_14402])).
% 11.70/4.81  tff(c_14464, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_14434])).
% 11.70/4.81  tff(c_14471, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_14464])).
% 11.70/4.81  tff(c_8879, plain, (![A_494, B_495, C_496]: (m1_subset_1(k2_relset_1(A_494, B_495, C_496), k1_zfmisc_1(B_495)) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_494, B_495))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.70/4.81  tff(c_9278, plain, (![A_521, B_522, C_523]: (r1_tarski(k2_relset_1(A_521, B_522, C_523), B_522) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(resolution, [status(thm)], [c_8879, c_20])).
% 11.70/4.81  tff(c_9298, plain, (![A_521, B_522, A_7]: (r1_tarski(k2_relset_1(A_521, B_522, A_7), B_522) | ~r1_tarski(A_7, k2_zfmisc_1(A_521, B_522)))), inference(resolution, [status(thm)], [c_22, c_9278])).
% 11.70/4.81  tff(c_14479, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14471, c_9298])).
% 11.70/4.81  tff(c_14957, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_14479])).
% 11.70/4.81  tff(c_15008, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14438, c_14957])).
% 11.70/4.81  tff(c_15011, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_15008])).
% 11.70/4.81  tff(c_15014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_8, c_15011])).
% 11.70/4.81  tff(c_15015, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14479])).
% 11.70/4.81  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.70/4.81  tff(c_15032, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_15015, c_4])).
% 11.70/4.81  tff(c_15084, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_15032])).
% 11.70/4.81  tff(c_15087, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_15084])).
% 11.70/4.81  tff(c_15090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_8, c_15087])).
% 11.70/4.81  tff(c_15091, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_15032])).
% 11.70/4.81  tff(c_68, plain, (![B_38, A_37]: (v1_funct_2(B_38, k1_relat_1(B_38), A_37) | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.70/4.81  tff(c_14414, plain, (![A_37]: (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), A_37) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_37) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14378, c_68])).
% 11.70/4.81  tff(c_14442, plain, (![A_37]: (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), A_37) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_13858, c_9635, c_14414])).
% 11.70/4.81  tff(c_15101, plain, (![A_37]: (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), A_37) | ~r1_tarski(k1_relat_1('#skF_3'), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_15091, c_14442])).
% 11.70/4.81  tff(c_14379, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14369])).
% 11.70/4.81  tff(c_15102, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15091, c_14471])).
% 11.70/4.81  tff(c_15250, plain, (![A_814]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), A_814)) | ~r1_tarski(k1_relat_1('#skF_3'), A_814))), inference(demodulation, [status(thm), theory('equality')], [c_15091, c_14438])).
% 11.70/4.81  tff(c_10063, plain, (![C_583]: (m1_subset_1(k2_funct_1(C_583), k1_zfmisc_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), C_583)!=k2_struct_0('#skF_1') | ~v2_funct_1(C_583) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_583, k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_583))), inference(superposition, [status(thm), theory('equality')], [c_8616, c_9736])).
% 11.70/4.81  tff(c_10083, plain, (![A_7]: (m1_subset_1(k2_funct_1(A_7), k1_zfmisc_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), A_7)!=k2_struct_0('#skF_1') | ~v2_funct_1(A_7) | ~v1_funct_2(A_7, k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | ~v1_funct_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_10063])).
% 11.70/4.81  tff(c_14742, plain, (![A_7]: (m1_subset_1(k2_funct_1(A_7), k1_zfmisc_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), A_7)!=k1_relat_1('#skF_3') | ~v2_funct_1(A_7) | ~v1_funct_2(A_7, k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_10538, c_10538, c_10538, c_10538, c_10083])).
% 11.70/4.81  tff(c_15254, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15250, c_14742])).
% 11.70/4.81  tff(c_15280, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9635, c_14379, c_15102, c_15254])).
% 11.70/4.81  tff(c_15660, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15280])).
% 11.70/4.81  tff(c_15663, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15101, c_15660])).
% 11.70/4.81  tff(c_15676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_15663])).
% 11.70/4.81  tff(c_15678, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15280])).
% 11.70/4.81  tff(c_15677, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15280])).
% 11.70/4.81  tff(c_15692, plain, (r1_tarski(k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_15677, c_20])).
% 11.70/4.81  tff(c_15761, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_15692, c_4])).
% 11.70/4.81  tff(c_16039, plain, (~r1_tarski('#skF_3', k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_15761])).
% 11.70/4.81  tff(c_16042, plain, (~r1_tarski('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_16039])).
% 11.70/4.81  tff(c_16045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_88, c_80, c_8, c_16042])).
% 11.70/4.81  tff(c_16046, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_15761])).
% 11.70/4.81  tff(c_14411, plain, (![A_37]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), A_37))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_37) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_14378, c_66])).
% 11.70/4.81  tff(c_14440, plain, (![A_37]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), A_37))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_13858, c_9635, c_14411])).
% 11.70/4.81  tff(c_15097, plain, (![A_37]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), A_37))) | ~r1_tarski(k1_relat_1('#skF_3'), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_15091, c_14440])).
% 11.70/4.81  tff(c_48, plain, (![A_20, B_21, C_22]: (m1_subset_1(k2_relset_1(A_20, B_21, C_22), k1_zfmisc_1(B_21)) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.70/4.81  tff(c_15233, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15102, c_48])).
% 11.70/4.81  tff(c_16297, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitLeft, [status(thm)], [c_15233])).
% 11.70/4.81  tff(c_16300, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15097, c_16297])).
% 11.70/4.81  tff(c_16310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_16300])).
% 11.70/4.81  tff(c_16312, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_15233])).
% 11.70/4.81  tff(c_76, plain, (![A_41, B_42, C_43]: (k2_tops_2(A_41, B_42, C_43)=k2_funct_1(C_43) | ~v2_funct_1(C_43) | k2_relset_1(A_41, B_42, C_43)!=B_42 | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_2(C_43, A_41, B_42) | ~v1_funct_1(C_43))), inference(cnfTransformation, [status(thm)], [f_192])).
% 11.70/4.81  tff(c_16363, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16312, c_76])).
% 11.70/4.81  tff(c_16400, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9635, c_15678, c_15102, c_14379, c_16046, c_16363])).
% 11.70/4.81  tff(c_9447, plain, (![A_533, B_534, C_535]: (k2_tops_2(A_533, B_534, C_535)=k2_funct_1(C_535) | ~v2_funct_1(C_535) | k2_relset_1(A_533, B_534, C_535)!=B_534 | ~m1_subset_1(C_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))) | ~v1_funct_2(C_535, A_533, B_534) | ~v1_funct_1(C_535))), inference(cnfTransformation, [status(thm)], [f_192])).
% 11.70/4.81  tff(c_9969, plain, (![C_575]: (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_575)=k2_funct_1(C_575) | ~v2_funct_1(C_575) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_575)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_575, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_575, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_575))), inference(superposition, [status(thm), theory('equality')], [c_8616, c_9447])).
% 11.70/4.81  tff(c_9972, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8620, c_9969])).
% 11.70/4.81  tff(c_9975, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8429, c_8618, c_80, c_9972])).
% 11.70/4.81  tff(c_8617, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8608, c_8608, c_8608, c_214])).
% 11.70/4.81  tff(c_9976, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9975, c_8617])).
% 11.70/4.81  tff(c_10545, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10538, c_10538, c_9976])).
% 11.70/4.81  tff(c_16416, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16400, c_10545])).
% 11.70/4.81  tff(c_22100, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_22097, c_16416])).
% 11.70/4.81  tff(c_22104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_10554, c_8429, c_22100])).
% 11.70/4.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.70/4.81  
% 11.70/4.81  Inference rules
% 11.70/4.81  ----------------------
% 11.70/4.81  #Ref     : 0
% 11.70/4.81  #Sup     : 4847
% 11.70/4.81  #Fact    : 0
% 11.70/4.81  #Define  : 0
% 11.70/4.81  #Split   : 32
% 11.70/4.81  #Chain   : 0
% 11.70/4.81  #Close   : 0
% 11.70/4.81  
% 11.70/4.81  Ordering : KBO
% 11.70/4.81  
% 11.70/4.81  Simplification rules
% 11.70/4.81  ----------------------
% 11.70/4.81  #Subsume      : 1117
% 11.70/4.81  #Demod        : 8738
% 11.70/4.81  #Tautology    : 1892
% 11.70/4.81  #SimpNegUnit  : 25
% 11.70/4.81  #BackRed      : 136
% 11.70/4.81  
% 11.70/4.81  #Partial instantiations: 0
% 11.70/4.81  #Strategies tried      : 1
% 11.70/4.81  
% 11.70/4.81  Timing (in seconds)
% 11.70/4.81  ----------------------
% 11.70/4.81  Preprocessing        : 0.37
% 11.70/4.81  Parsing              : 0.20
% 11.70/4.81  CNF conversion       : 0.02
% 11.70/4.81  Main loop            : 3.61
% 11.70/4.81  Inferencing          : 0.97
% 11.70/4.81  Reduction            : 1.47
% 11.70/4.81  Demodulation         : 1.15
% 11.70/4.81  BG Simplification    : 0.10
% 11.70/4.81  Subsumption          : 0.84
% 11.70/4.81  Abstraction          : 0.15
% 11.70/4.81  MUC search           : 0.00
% 11.70/4.81  Cooper               : 0.00
% 11.70/4.81  Total                : 4.08
% 11.70/4.81  Index Insertion      : 0.00
% 11.70/4.81  Index Deletion       : 0.00
% 11.70/4.81  Index Matching       : 0.00
% 12.10/4.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
