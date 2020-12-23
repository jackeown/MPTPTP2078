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
% DateTime   : Thu Dec  3 10:23:36 EST 2020

% Result     : Theorem 18.63s
% Output     : CNFRefutation 18.91s
% Verified   : 
% Statistics : Number of formulae       :  221 (24717 expanded)
%              Number of leaves         :   59 (8232 expanded)
%              Depth                    :   30
%              Number of atoms          :  483 (68491 expanded)
%              Number of equality atoms :  113 (14778 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_280,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_176,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_238,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_246,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_208,axiom,(
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

tff(f_178,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_224,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_234,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_126,axiom,(
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

tff(f_258,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_116,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_114,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48092,plain,(
    ! [C_1561,A_1562,B_1563] :
      ( v1_xboole_0(C_1561)
      | ~ m1_subset_1(C_1561,k1_zfmisc_1(k2_zfmisc_1(A_1562,B_1563)))
      | ~ v1_xboole_0(A_1562) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48105,plain,(
    ! [C_1561] :
      ( v1_xboole_0(C_1561)
      | ~ m1_subset_1(C_1561,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_48092])).

tff(c_48114,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_48105])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48108,plain,(
    ! [C_1561,A_2] :
      ( v1_xboole_0(C_1561)
      | ~ m1_subset_1(C_1561,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_48092])).

tff(c_48115,plain,(
    ! [A_2] : ~ v1_xboole_0(A_2) ),
    inference(splitLeft,[status(thm)],[c_48108])).

tff(c_72,plain,(
    ! [A_40,B_41] : v1_xboole_0('#skF_1'(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_48134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48115,c_72])).

tff(c_48136,plain,(
    ! [C_1565] :
      ( v1_xboole_0(C_1565)
      | ~ m1_subset_1(C_1565,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_48108])).

tff(c_48152,plain,(
    ! [A_1566] :
      ( v1_xboole_0(A_1566)
      | ~ r1_tarski(A_1566,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_48136])).

tff(c_48166,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_48152])).

tff(c_48175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48114,c_48166])).

tff(c_48177,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_48105])).

tff(c_112,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_118,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_166,plain,(
    ! [A_80] :
      ( u1_struct_0(A_80) = k2_struct_0(A_80)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_174,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_166])).

tff(c_173,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_166])).

tff(c_108,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_175,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_108])).

tff(c_338,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_175])).

tff(c_28151,plain,(
    ! [A_920,B_921,C_922] :
      ( k2_relset_1(A_920,B_921,C_922) = k2_relat_1(C_922)
      | ~ m1_subset_1(C_922,k1_zfmisc_1(k2_zfmisc_1(A_920,B_921))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28172,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_28151])).

tff(c_106,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_195,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_173,c_106])).

tff(c_28175,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28172,c_195])).

tff(c_98,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(k2_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_28190,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28175,c_98])).

tff(c_28194,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_28190])).

tff(c_28195,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_28194])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_341,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_338,c_14])).

tff(c_347,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_341])).

tff(c_420,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_437,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_338,c_420])).

tff(c_28001,plain,(
    ! [B_909,A_910] :
      ( k1_relat_1(B_909) = A_910
      | ~ v1_partfun1(B_909,A_910)
      | ~ v4_relat_1(B_909,A_910)
      | ~ v1_relat_1(B_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_28016,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_437,c_28001])).

tff(c_28032,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_28016])).

tff(c_28042,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28032])).

tff(c_110,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_176,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_110])).

tff(c_185,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_176])).

tff(c_28185,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28175,c_185])).

tff(c_28183,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28175,c_338])).

tff(c_58,plain,(
    ! [C_37,A_34,B_35] :
      ( v1_partfun1(C_37,A_34)
      | ~ v1_funct_2(C_37,A_34,B_35)
      | ~ v1_funct_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | v1_xboole_0(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_28256,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28183,c_58])).

tff(c_28277,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28185,c_28256])).

tff(c_28279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28195,c_28042,c_28277])).

tff(c_28280,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28032])).

tff(c_28285,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28280,c_338])).

tff(c_56,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28368,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28285,c_56])).

tff(c_28287,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28280,c_195])).

tff(c_28394,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28368,c_28287])).

tff(c_28288,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28280,c_185])).

tff(c_28403,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28394,c_28288])).

tff(c_28401,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28394,c_28285])).

tff(c_29509,plain,(
    ! [A_1015,B_1016,C_1017,D_1018] :
      ( r2_funct_2(A_1015,B_1016,C_1017,C_1017)
      | ~ m1_subset_1(D_1018,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1016)))
      | ~ v1_funct_2(D_1018,A_1015,B_1016)
      | ~ v1_funct_1(D_1018)
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1016)))
      | ~ v1_funct_2(C_1017,A_1015,B_1016)
      | ~ v1_funct_1(C_1017) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_29513,plain,(
    ! [C_1017] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),C_1017,C_1017)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_1017,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_1017,k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(C_1017) ) ),
    inference(resolution,[status(thm)],[c_28401,c_29509])).

tff(c_29595,plain,(
    ! [C_1019] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),C_1019,C_1019)
      | ~ m1_subset_1(C_1019,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_1019,k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(C_1019) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_29513])).

tff(c_29600,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28401,c_29595])).

tff(c_29613,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_29600])).

tff(c_104,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_28,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28399,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28394,c_28368])).

tff(c_28701,plain,(
    ! [C_957,A_958,B_959] :
      ( v1_funct_1(k2_funct_1(C_957))
      | k2_relset_1(A_958,B_959,C_957) != B_959
      | ~ v2_funct_1(C_957)
      | ~ m1_subset_1(C_957,k1_zfmisc_1(k2_zfmisc_1(A_958,B_959)))
      | ~ v1_funct_2(C_957,A_958,B_959)
      | ~ v1_funct_1(C_957) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_28704,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28401,c_28701])).

tff(c_28723,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_104,c_28399,c_28704])).

tff(c_76,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_32,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_32])).

tff(c_22,plain,(
    ! [A_13] :
      ( k1_relat_1(A_13) = k1_xboole_0
      | k2_relat_1(A_13) != k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_355,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_347,c_22])).

tff(c_363,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_29321,plain,(
    ! [B_1006,C_1007,A_1008] :
      ( k6_partfun1(B_1006) = k5_relat_1(k2_funct_1(C_1007),C_1007)
      | k1_xboole_0 = B_1006
      | ~ v2_funct_1(C_1007)
      | k2_relset_1(A_1008,B_1006,C_1007) != B_1006
      | ~ m1_subset_1(C_1007,k1_zfmisc_1(k2_zfmisc_1(A_1008,B_1006)))
      | ~ v1_funct_2(C_1007,A_1008,B_1006)
      | ~ v1_funct_1(C_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_29325,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28401,c_29321])).

tff(c_29340,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_28399,c_104,c_29325])).

tff(c_29341,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_29340])).

tff(c_42,plain,(
    ! [B_19,A_17] :
      ( v2_funct_1(B_19)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(k5_relat_1(B_19,A_17))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_29352,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1(k2_relat_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_29341,c_42])).

tff(c_29363,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_28723,c_120,c_29352])).

tff(c_29481,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_29363])).

tff(c_29484,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_29481])).

tff(c_29488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_29484])).

tff(c_29490,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29363])).

tff(c_44,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_29489,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29363])).

tff(c_29499,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_29489])).

tff(c_29502,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_29499])).

tff(c_29506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_104,c_29502])).

tff(c_29507,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29489])).

tff(c_46,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_29508,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_29489])).

tff(c_28426,plain,(
    ! [A_930] :
      ( m1_subset_1(A_930,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_930),k2_relat_1(A_930))))
      | ~ v1_funct_1(A_930)
      | ~ v1_relat_1(A_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29626,plain,(
    ! [A_1020] :
      ( r1_tarski(A_1020,k2_zfmisc_1(k1_relat_1(A_1020),k2_relat_1(A_1020)))
      | ~ v1_funct_1(A_1020)
      | ~ v1_relat_1(A_1020) ) ),
    inference(resolution,[status(thm)],[c_28426,c_10])).

tff(c_29645,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29508,c_29626])).

tff(c_29669,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29490,c_28723,c_29645])).

tff(c_440,plain,(
    ! [A_4,A_117,B_118] :
      ( v4_relat_1(A_4,A_117)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_117,B_118)) ) ),
    inference(resolution,[status(thm)],[c_12,c_420])).

tff(c_29757,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_29669,c_440])).

tff(c_62,plain,(
    ! [B_39] :
      ( v1_partfun1(B_39,k1_relat_1(B_39))
      | ~ v4_relat_1(B_39,k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_29768,plain,
    ( v1_partfun1(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_29757,c_62])).

tff(c_29778,plain,(
    v1_partfun1(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29490,c_29768])).

tff(c_29834,plain,
    ( v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_29778])).

tff(c_29836,plain,(
    v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_104,c_29834])).

tff(c_29771,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_29757])).

tff(c_29780,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_104,c_29771])).

tff(c_64,plain,(
    ! [B_39,A_38] :
      ( k1_relat_1(B_39) = A_38
      | ~ v1_partfun1(B_39,A_38)
      | ~ v4_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_29783,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_29780,c_64])).

tff(c_29786,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29490,c_29783])).

tff(c_30554,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29836,c_29786])).

tff(c_29439,plain,(
    ! [A_1012,C_1013,B_1014] :
      ( k6_partfun1(A_1012) = k5_relat_1(C_1013,k2_funct_1(C_1013))
      | k1_xboole_0 = B_1014
      | ~ v2_funct_1(C_1013)
      | k2_relset_1(A_1012,B_1014,C_1013) != B_1014
      | ~ m1_subset_1(C_1013,k1_zfmisc_1(k2_zfmisc_1(A_1012,B_1014)))
      | ~ v1_funct_2(C_1013,A_1012,B_1014)
      | ~ v1_funct_1(C_1013) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_29443,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28401,c_29439])).

tff(c_29458,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_28399,c_104,c_29443])).

tff(c_29459,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_29458])).

tff(c_48,plain,(
    ! [A_21,B_23] :
      ( k2_funct_1(A_21) = B_23
      | k6_relat_1(k2_relat_1(A_21)) != k5_relat_1(B_23,A_21)
      | k2_relat_1(B_23) != k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28812,plain,(
    ! [A_967,B_968] :
      ( k2_funct_1(A_967) = B_968
      | k6_partfun1(k2_relat_1(A_967)) != k5_relat_1(B_968,A_967)
      | k2_relat_1(B_968) != k1_relat_1(A_967)
      | ~ v2_funct_1(A_967)
      | ~ v1_funct_1(B_968)
      | ~ v1_relat_1(B_968)
      | ~ v1_funct_1(A_967)
      | ~ v1_relat_1(A_967) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_48])).

tff(c_47486,plain,(
    ! [A_1499,B_1500] :
      ( k2_funct_1(k2_funct_1(A_1499)) = B_1500
      | k5_relat_1(B_1500,k2_funct_1(A_1499)) != k6_partfun1(k1_relat_1(A_1499))
      | k2_relat_1(B_1500) != k1_relat_1(k2_funct_1(A_1499))
      | ~ v2_funct_1(k2_funct_1(A_1499))
      | ~ v1_funct_1(B_1500)
      | ~ v1_relat_1(B_1500)
      | ~ v1_funct_1(k2_funct_1(A_1499))
      | ~ v1_relat_1(k2_funct_1(A_1499))
      | ~ v2_funct_1(A_1499)
      | ~ v1_funct_1(A_1499)
      | ~ v1_relat_1(A_1499) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_28812])).

tff(c_47496,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_29459,c_47486])).

tff(c_47509,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_104,c_29490,c_28723,c_29507,c_30554,c_47496])).

tff(c_28890,plain,(
    ! [C_975,B_976,A_977] :
      ( v1_funct_2(k2_funct_1(C_975),B_976,A_977)
      | k2_relset_1(A_977,B_976,C_975) != B_976
      | ~ v2_funct_1(C_975)
      | ~ m1_subset_1(C_975,k1_zfmisc_1(k2_zfmisc_1(A_977,B_976)))
      | ~ v1_funct_2(C_975,A_977,B_976)
      | ~ v1_funct_1(C_975) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_28893,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28401,c_28890])).

tff(c_28912,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_104,c_28399,c_28893])).

tff(c_29753,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_29669])).

tff(c_29762,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_104,c_29753])).

tff(c_28334,plain,(
    ! [A_926,B_927,C_928] :
      ( k2_relset_1(A_926,B_927,C_928) = k2_relat_1(C_928)
      | ~ m1_subset_1(C_928,k1_zfmisc_1(k2_zfmisc_1(A_926,B_927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28349,plain,(
    ! [A_926,B_927,A_4] :
      ( k2_relset_1(A_926,B_927,A_4) = k2_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_926,B_927)) ) ),
    inference(resolution,[status(thm)],[c_12,c_28334])).

tff(c_29846,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_29762,c_28349])).

tff(c_29860,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29508,c_29846])).

tff(c_90,plain,(
    ! [A_54] :
      ( m1_subset_1(A_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54),k2_relat_1(A_54))))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_29545,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29508,c_90])).

tff(c_29573,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29490,c_28723,c_29545])).

tff(c_30000,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_29573])).

tff(c_30037,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_112,c_104,c_30000])).

tff(c_100,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_tops_2(A_57,B_58,C_59) = k2_funct_1(C_59)
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_30323,plain,
    ( k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30037,c_100])).

tff(c_30364,plain,(
    k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28723,c_28912,c_29860,c_29507,c_30323])).

tff(c_28974,plain,(
    ! [A_980,B_981,C_982] :
      ( k2_tops_2(A_980,B_981,C_982) = k2_funct_1(C_982)
      | ~ v2_funct_1(C_982)
      | k2_relset_1(A_980,B_981,C_982) != B_981
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(A_980,B_981)))
      | ~ v1_funct_2(C_982,A_980,B_981)
      | ~ v1_funct_1(C_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_28977,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28401,c_28974])).

tff(c_28996,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_28403,c_28399,c_104,c_28977])).

tff(c_102,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_268,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_174,c_174,c_173,c_173,c_173,c_102])).

tff(c_28286,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28280,c_28280,c_28280,c_268])).

tff(c_28400,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28394,c_28394,c_28394,c_28286])).

tff(c_29028,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28996,c_28400])).

tff(c_30548,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30364,c_29028])).

tff(c_47530,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47509,c_30548])).

tff(c_47549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29613,c_47530])).

tff(c_47551,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_48485,plain,(
    ! [A_1588,B_1589,C_1590] :
      ( k2_relset_1(A_1588,B_1589,C_1590) = k2_relat_1(C_1590)
      | ~ m1_subset_1(C_1590,k1_zfmisc_1(k2_zfmisc_1(A_1588,B_1589))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48491,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_48485])).

tff(c_48507,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47551,c_48491])).

tff(c_48516,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48507,c_195])).

tff(c_48532,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48516,c_98])).

tff(c_48536,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_48177,c_48532])).

tff(c_48538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_48536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.63/10.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.63/10.07  
% 18.63/10.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.63/10.08  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 18.63/10.08  
% 18.63/10.08  %Foreground sorts:
% 18.63/10.08  
% 18.63/10.08  
% 18.63/10.08  %Background operators:
% 18.63/10.08  
% 18.63/10.08  
% 18.63/10.08  %Foreground operators:
% 18.63/10.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.63/10.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 18.63/10.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.63/10.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.63/10.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.63/10.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.63/10.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.63/10.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.63/10.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.63/10.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.63/10.08  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 18.63/10.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.63/10.08  tff('#skF_2', type, '#skF_2': $i).
% 18.63/10.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 18.63/10.08  tff('#skF_3', type, '#skF_3': $i).
% 18.63/10.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.63/10.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.63/10.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 18.63/10.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 18.63/10.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.63/10.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.63/10.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.63/10.08  tff('#skF_4', type, '#skF_4': $i).
% 18.63/10.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.63/10.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.63/10.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.63/10.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.63/10.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.63/10.08  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 18.63/10.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.63/10.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.63/10.08  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 18.63/10.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.63/10.08  
% 18.91/10.10  tff(f_280, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 18.91/10.10  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 18.91/10.10  tff(f_139, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 18.91/10.10  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.91/10.10  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.91/10.10  tff(f_176, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 18.91/10.10  tff(f_238, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 18.91/10.10  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.91/10.10  tff(f_246, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 18.91/10.10  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 18.91/10.10  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 18.91/10.10  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.91/10.10  tff(f_165, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 18.91/10.10  tff(f_157, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 18.91/10.10  tff(f_192, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 18.91/10.10  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.91/10.10  tff(f_208, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 18.91/10.10  tff(f_178, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.91/10.10  tff(f_70, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 18.91/10.10  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 18.91/10.10  tff(f_224, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 18.91/10.10  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 18.91/10.10  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 18.91/10.10  tff(f_234, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 18.91/10.10  tff(f_126, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 18.91/10.10  tff(f_258, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 18.91/10.10  tff(c_116, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.10  tff(c_114, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.10  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.91/10.10  tff(c_48092, plain, (![C_1561, A_1562, B_1563]: (v1_xboole_0(C_1561) | ~m1_subset_1(C_1561, k1_zfmisc_1(k2_zfmisc_1(A_1562, B_1563))) | ~v1_xboole_0(A_1562))), inference(cnfTransformation, [status(thm)], [f_139])).
% 18.91/10.10  tff(c_48105, plain, (![C_1561]: (v1_xboole_0(C_1561) | ~m1_subset_1(C_1561, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_48092])).
% 18.91/10.10  tff(c_48114, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_48105])).
% 18.91/10.10  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.91/10.10  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.91/10.10  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.91/10.10  tff(c_48108, plain, (![C_1561, A_2]: (v1_xboole_0(C_1561) | ~m1_subset_1(C_1561, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(A_2))), inference(superposition, [status(thm), theory('equality')], [c_6, c_48092])).
% 18.91/10.10  tff(c_48115, plain, (![A_2]: (~v1_xboole_0(A_2))), inference(splitLeft, [status(thm)], [c_48108])).
% 18.91/10.10  tff(c_72, plain, (![A_40, B_41]: (v1_xboole_0('#skF_1'(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_176])).
% 18.91/10.10  tff(c_48134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48115, c_72])).
% 18.91/10.10  tff(c_48136, plain, (![C_1565]: (v1_xboole_0(C_1565) | ~m1_subset_1(C_1565, k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_48108])).
% 18.91/10.10  tff(c_48152, plain, (![A_1566]: (v1_xboole_0(A_1566) | ~r1_tarski(A_1566, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_48136])).
% 18.91/10.10  tff(c_48166, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_48152])).
% 18.91/10.11  tff(c_48175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48114, c_48166])).
% 18.91/10.11  tff(c_48177, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_48105])).
% 18.91/10.11  tff(c_112, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_118, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_166, plain, (![A_80]: (u1_struct_0(A_80)=k2_struct_0(A_80) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_238])).
% 18.91/10.11  tff(c_174, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_118, c_166])).
% 18.91/10.11  tff(c_173, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_114, c_166])).
% 18.91/10.11  tff(c_108, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_175, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_108])).
% 18.91/10.11  tff(c_338, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_175])).
% 18.91/10.11  tff(c_28151, plain, (![A_920, B_921, C_922]: (k2_relset_1(A_920, B_921, C_922)=k2_relat_1(C_922) | ~m1_subset_1(C_922, k1_zfmisc_1(k2_zfmisc_1(A_920, B_921))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.91/10.11  tff(c_28172, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_338, c_28151])).
% 18.91/10.11  tff(c_106, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_195, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_173, c_106])).
% 18.91/10.11  tff(c_28175, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28172, c_195])).
% 18.91/10.11  tff(c_98, plain, (![A_56]: (~v1_xboole_0(k2_struct_0(A_56)) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_246])).
% 18.91/10.11  tff(c_28190, plain, (~v1_xboole_0(k2_relat_1('#skF_4')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28175, c_98])).
% 18.91/10.11  tff(c_28194, plain, (~v1_xboole_0(k2_relat_1('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_28190])).
% 18.91/10.11  tff(c_28195, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_116, c_28194])).
% 18.91/10.11  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.91/10.11  tff(c_14, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.91/10.11  tff(c_341, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_338, c_14])).
% 18.91/10.11  tff(c_347, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_341])).
% 18.91/10.11  tff(c_420, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 18.91/10.11  tff(c_437, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_338, c_420])).
% 18.91/10.11  tff(c_28001, plain, (![B_909, A_910]: (k1_relat_1(B_909)=A_910 | ~v1_partfun1(B_909, A_910) | ~v4_relat_1(B_909, A_910) | ~v1_relat_1(B_909))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.91/10.11  tff(c_28016, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_437, c_28001])).
% 18.91/10.11  tff(c_28032, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_28016])).
% 18.91/10.11  tff(c_28042, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_28032])).
% 18.91/10.11  tff(c_110, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_176, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_110])).
% 18.91/10.11  tff(c_185, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_176])).
% 18.91/10.11  tff(c_28185, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28175, c_185])).
% 18.91/10.11  tff(c_28183, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_28175, c_338])).
% 18.91/10.11  tff(c_58, plain, (![C_37, A_34, B_35]: (v1_partfun1(C_37, A_34) | ~v1_funct_2(C_37, A_34, B_35) | ~v1_funct_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | v1_xboole_0(B_35))), inference(cnfTransformation, [status(thm)], [f_157])).
% 18.91/10.11  tff(c_28256, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28183, c_58])).
% 18.91/10.11  tff(c_28277, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28185, c_28256])).
% 18.91/10.11  tff(c_28279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28195, c_28042, c_28277])).
% 18.91/10.11  tff(c_28280, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_28032])).
% 18.91/10.11  tff(c_28285, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_28280, c_338])).
% 18.91/10.11  tff(c_56, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.91/10.11  tff(c_28368, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28285, c_56])).
% 18.91/10.11  tff(c_28287, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28280, c_195])).
% 18.91/10.11  tff(c_28394, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28368, c_28287])).
% 18.91/10.11  tff(c_28288, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28280, c_185])).
% 18.91/10.11  tff(c_28403, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28394, c_28288])).
% 18.91/10.11  tff(c_28401, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_28394, c_28285])).
% 18.91/10.11  tff(c_29509, plain, (![A_1015, B_1016, C_1017, D_1018]: (r2_funct_2(A_1015, B_1016, C_1017, C_1017) | ~m1_subset_1(D_1018, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1016))) | ~v1_funct_2(D_1018, A_1015, B_1016) | ~v1_funct_1(D_1018) | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1016))) | ~v1_funct_2(C_1017, A_1015, B_1016) | ~v1_funct_1(C_1017))), inference(cnfTransformation, [status(thm)], [f_192])).
% 18.91/10.11  tff(c_29513, plain, (![C_1017]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), C_1017, C_1017) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_1017, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2(C_1017, k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(C_1017))), inference(resolution, [status(thm)], [c_28401, c_29509])).
% 18.91/10.11  tff(c_29595, plain, (![C_1019]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), C_1019, C_1019) | ~m1_subset_1(C_1019, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2(C_1019, k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(C_1019))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_29513])).
% 18.91/10.11  tff(c_29600, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28401, c_29595])).
% 18.91/10.11  tff(c_29613, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_29600])).
% 18.91/10.11  tff(c_104, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_28, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.91/10.11  tff(c_28399, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28394, c_28368])).
% 18.91/10.11  tff(c_28701, plain, (![C_957, A_958, B_959]: (v1_funct_1(k2_funct_1(C_957)) | k2_relset_1(A_958, B_959, C_957)!=B_959 | ~v2_funct_1(C_957) | ~m1_subset_1(C_957, k1_zfmisc_1(k2_zfmisc_1(A_958, B_959))) | ~v1_funct_2(C_957, A_958, B_959) | ~v1_funct_1(C_957))), inference(cnfTransformation, [status(thm)], [f_208])).
% 18.91/10.11  tff(c_28704, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28401, c_28701])).
% 18.91/10.11  tff(c_28723, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_104, c_28399, c_28704])).
% 18.91/10.11  tff(c_76, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_178])).
% 18.91/10.11  tff(c_32, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.91/10.11  tff(c_120, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_32])).
% 18.91/10.11  tff(c_22, plain, (![A_13]: (k1_relat_1(A_13)=k1_xboole_0 | k2_relat_1(A_13)!=k1_xboole_0 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.91/10.11  tff(c_355, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_347, c_22])).
% 18.91/10.11  tff(c_363, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_355])).
% 18.91/10.11  tff(c_29321, plain, (![B_1006, C_1007, A_1008]: (k6_partfun1(B_1006)=k5_relat_1(k2_funct_1(C_1007), C_1007) | k1_xboole_0=B_1006 | ~v2_funct_1(C_1007) | k2_relset_1(A_1008, B_1006, C_1007)!=B_1006 | ~m1_subset_1(C_1007, k1_zfmisc_1(k2_zfmisc_1(A_1008, B_1006))) | ~v1_funct_2(C_1007, A_1008, B_1006) | ~v1_funct_1(C_1007))), inference(cnfTransformation, [status(thm)], [f_224])).
% 18.91/10.11  tff(c_29325, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0 | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28401, c_29321])).
% 18.91/10.11  tff(c_29340, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_28399, c_104, c_29325])).
% 18.91/10.11  tff(c_29341, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_363, c_29340])).
% 18.91/10.11  tff(c_42, plain, (![B_19, A_17]: (v2_funct_1(B_19) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(k5_relat_1(B_19, A_17)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.91/10.11  tff(c_29352, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1(k2_relat_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29341, c_42])).
% 18.91/10.11  tff(c_29363, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_28723, c_120, c_29352])).
% 18.91/10.11  tff(c_29481, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_29363])).
% 18.91/10.11  tff(c_29484, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_29481])).
% 18.91/10.11  tff(c_29488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_29484])).
% 18.91/10.11  tff(c_29490, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29363])).
% 18.91/10.11  tff(c_44, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_109])).
% 18.91/10.11  tff(c_29489, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29363])).
% 18.91/10.11  tff(c_29499, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_29489])).
% 18.91/10.11  tff(c_29502, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_29499])).
% 18.91/10.11  tff(c_29506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_104, c_29502])).
% 18.91/10.11  tff(c_29507, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29489])).
% 18.91/10.11  tff(c_46, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_109])).
% 18.91/10.11  tff(c_29508, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_29489])).
% 18.91/10.11  tff(c_28426, plain, (![A_930]: (m1_subset_1(A_930, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_930), k2_relat_1(A_930)))) | ~v1_funct_1(A_930) | ~v1_relat_1(A_930))), inference(cnfTransformation, [status(thm)], [f_234])).
% 18.91/10.11  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.91/10.11  tff(c_29626, plain, (![A_1020]: (r1_tarski(A_1020, k2_zfmisc_1(k1_relat_1(A_1020), k2_relat_1(A_1020))) | ~v1_funct_1(A_1020) | ~v1_relat_1(A_1020))), inference(resolution, [status(thm)], [c_28426, c_10])).
% 18.91/10.11  tff(c_29645, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29508, c_29626])).
% 18.91/10.11  tff(c_29669, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_29490, c_28723, c_29645])).
% 18.91/10.11  tff(c_440, plain, (![A_4, A_117, B_118]: (v4_relat_1(A_4, A_117) | ~r1_tarski(A_4, k2_zfmisc_1(A_117, B_118)))), inference(resolution, [status(thm)], [c_12, c_420])).
% 18.91/10.11  tff(c_29757, plain, (v4_relat_1(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_29669, c_440])).
% 18.91/10.11  tff(c_62, plain, (![B_39]: (v1_partfun1(B_39, k1_relat_1(B_39)) | ~v4_relat_1(B_39, k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.91/10.11  tff(c_29768, plain, (v1_partfun1(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29757, c_62])).
% 18.91/10.11  tff(c_29778, plain, (v1_partfun1(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_29490, c_29768])).
% 18.91/10.11  tff(c_29834, plain, (v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_29778])).
% 18.91/10.11  tff(c_29836, plain, (v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_104, c_29834])).
% 18.91/10.11  tff(c_29771, plain, (v4_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_29757])).
% 18.91/10.11  tff(c_29780, plain, (v4_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_104, c_29771])).
% 18.91/10.11  tff(c_64, plain, (![B_39, A_38]: (k1_relat_1(B_39)=A_38 | ~v1_partfun1(B_39, A_38) | ~v4_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.91/10.11  tff(c_29783, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29780, c_64])).
% 18.91/10.11  tff(c_29786, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_29490, c_29783])).
% 18.91/10.11  tff(c_30554, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29836, c_29786])).
% 18.91/10.11  tff(c_29439, plain, (![A_1012, C_1013, B_1014]: (k6_partfun1(A_1012)=k5_relat_1(C_1013, k2_funct_1(C_1013)) | k1_xboole_0=B_1014 | ~v2_funct_1(C_1013) | k2_relset_1(A_1012, B_1014, C_1013)!=B_1014 | ~m1_subset_1(C_1013, k1_zfmisc_1(k2_zfmisc_1(A_1012, B_1014))) | ~v1_funct_2(C_1013, A_1012, B_1014) | ~v1_funct_1(C_1013))), inference(cnfTransformation, [status(thm)], [f_224])).
% 18.91/10.11  tff(c_29443, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0 | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28401, c_29439])).
% 18.91/10.11  tff(c_29458, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_28399, c_104, c_29443])).
% 18.91/10.11  tff(c_29459, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_363, c_29458])).
% 18.91/10.11  tff(c_48, plain, (![A_21, B_23]: (k2_funct_1(A_21)=B_23 | k6_relat_1(k2_relat_1(A_21))!=k5_relat_1(B_23, A_21) | k2_relat_1(B_23)!=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_126])).
% 18.91/10.11  tff(c_28812, plain, (![A_967, B_968]: (k2_funct_1(A_967)=B_968 | k6_partfun1(k2_relat_1(A_967))!=k5_relat_1(B_968, A_967) | k2_relat_1(B_968)!=k1_relat_1(A_967) | ~v2_funct_1(A_967) | ~v1_funct_1(B_968) | ~v1_relat_1(B_968) | ~v1_funct_1(A_967) | ~v1_relat_1(A_967))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_48])).
% 18.91/10.11  tff(c_47486, plain, (![A_1499, B_1500]: (k2_funct_1(k2_funct_1(A_1499))=B_1500 | k5_relat_1(B_1500, k2_funct_1(A_1499))!=k6_partfun1(k1_relat_1(A_1499)) | k2_relat_1(B_1500)!=k1_relat_1(k2_funct_1(A_1499)) | ~v2_funct_1(k2_funct_1(A_1499)) | ~v1_funct_1(B_1500) | ~v1_relat_1(B_1500) | ~v1_funct_1(k2_funct_1(A_1499)) | ~v1_relat_1(k2_funct_1(A_1499)) | ~v2_funct_1(A_1499) | ~v1_funct_1(A_1499) | ~v1_relat_1(A_1499))), inference(superposition, [status(thm), theory('equality')], [c_44, c_28812])).
% 18.91/10.11  tff(c_47496, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29459, c_47486])).
% 18.91/10.11  tff(c_47509, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_104, c_29490, c_28723, c_29507, c_30554, c_47496])).
% 18.91/10.11  tff(c_28890, plain, (![C_975, B_976, A_977]: (v1_funct_2(k2_funct_1(C_975), B_976, A_977) | k2_relset_1(A_977, B_976, C_975)!=B_976 | ~v2_funct_1(C_975) | ~m1_subset_1(C_975, k1_zfmisc_1(k2_zfmisc_1(A_977, B_976))) | ~v1_funct_2(C_975, A_977, B_976) | ~v1_funct_1(C_975))), inference(cnfTransformation, [status(thm)], [f_208])).
% 18.91/10.11  tff(c_28893, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28401, c_28890])).
% 18.91/10.11  tff(c_28912, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_104, c_28399, c_28893])).
% 18.91/10.11  tff(c_29753, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_29669])).
% 18.91/10.11  tff(c_29762, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_104, c_29753])).
% 18.91/10.11  tff(c_28334, plain, (![A_926, B_927, C_928]: (k2_relset_1(A_926, B_927, C_928)=k2_relat_1(C_928) | ~m1_subset_1(C_928, k1_zfmisc_1(k2_zfmisc_1(A_926, B_927))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.91/10.11  tff(c_28349, plain, (![A_926, B_927, A_4]: (k2_relset_1(A_926, B_927, A_4)=k2_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_926, B_927)))), inference(resolution, [status(thm)], [c_12, c_28334])).
% 18.91/10.11  tff(c_29846, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29762, c_28349])).
% 18.91/10.11  tff(c_29860, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29508, c_29846])).
% 18.91/10.11  tff(c_90, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54), k2_relat_1(A_54)))) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_234])).
% 18.91/10.11  tff(c_29545, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29508, c_90])).
% 18.91/10.11  tff(c_29573, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_29490, c_28723, c_29545])).
% 18.91/10.11  tff(c_30000, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_29573])).
% 18.91/10.11  tff(c_30037, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_112, c_104, c_30000])).
% 18.91/10.11  tff(c_100, plain, (![A_57, B_58, C_59]: (k2_tops_2(A_57, B_58, C_59)=k2_funct_1(C_59) | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_258])).
% 18.91/10.11  tff(c_30323, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30037, c_100])).
% 18.91/10.11  tff(c_30364, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28723, c_28912, c_29860, c_29507, c_30323])).
% 18.91/10.11  tff(c_28974, plain, (![A_980, B_981, C_982]: (k2_tops_2(A_980, B_981, C_982)=k2_funct_1(C_982) | ~v2_funct_1(C_982) | k2_relset_1(A_980, B_981, C_982)!=B_981 | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(A_980, B_981))) | ~v1_funct_2(C_982, A_980, B_981) | ~v1_funct_1(C_982))), inference(cnfTransformation, [status(thm)], [f_258])).
% 18.91/10.11  tff(c_28977, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28401, c_28974])).
% 18.91/10.11  tff(c_28996, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_28403, c_28399, c_104, c_28977])).
% 18.91/10.11  tff(c_102, plain, (~r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_280])).
% 18.91/10.11  tff(c_268, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_174, c_174, c_173, c_173, c_173, c_102])).
% 18.91/10.11  tff(c_28286, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28280, c_28280, c_28280, c_268])).
% 18.91/10.11  tff(c_28400, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28394, c_28394, c_28394, c_28286])).
% 18.91/10.11  tff(c_29028, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28996, c_28400])).
% 18.91/10.11  tff(c_30548, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30364, c_29028])).
% 18.91/10.11  tff(c_47530, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47509, c_30548])).
% 18.91/10.11  tff(c_47549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29613, c_47530])).
% 18.91/10.11  tff(c_47551, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_355])).
% 18.91/10.11  tff(c_48485, plain, (![A_1588, B_1589, C_1590]: (k2_relset_1(A_1588, B_1589, C_1590)=k2_relat_1(C_1590) | ~m1_subset_1(C_1590, k1_zfmisc_1(k2_zfmisc_1(A_1588, B_1589))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.91/10.11  tff(c_48491, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_338, c_48485])).
% 18.91/10.11  tff(c_48507, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47551, c_48491])).
% 18.91/10.11  tff(c_48516, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48507, c_195])).
% 18.91/10.11  tff(c_48532, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48516, c_98])).
% 18.91/10.11  tff(c_48536, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_48177, c_48532])).
% 18.91/10.11  tff(c_48538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_48536])).
% 18.91/10.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.91/10.11  
% 18.91/10.11  Inference rules
% 18.91/10.11  ----------------------
% 18.91/10.11  #Ref     : 0
% 18.91/10.11  #Sup     : 9679
% 18.91/10.11  #Fact    : 0
% 18.91/10.11  #Define  : 0
% 18.91/10.11  #Split   : 169
% 18.91/10.11  #Chain   : 0
% 18.91/10.11  #Close   : 0
% 18.91/10.11  
% 18.91/10.11  Ordering : KBO
% 18.91/10.11  
% 18.91/10.11  Simplification rules
% 18.91/10.11  ----------------------
% 18.91/10.11  #Subsume      : 4368
% 18.91/10.11  #Demod        : 14364
% 18.91/10.11  #Tautology    : 3950
% 18.91/10.11  #SimpNegUnit  : 2131
% 18.91/10.11  #BackRed      : 1506
% 18.91/10.11  
% 18.91/10.11  #Partial instantiations: 0
% 18.91/10.11  #Strategies tried      : 1
% 18.91/10.11  
% 18.91/10.11  Timing (in seconds)
% 18.91/10.11  ----------------------
% 18.91/10.11  Preprocessing        : 0.41
% 18.91/10.11  Parsing              : 0.22
% 18.91/10.11  CNF conversion       : 0.03
% 18.91/10.11  Main loop            : 8.90
% 18.91/10.11  Inferencing          : 1.85
% 18.91/10.11  Reduction            : 4.20
% 18.91/10.11  Demodulation         : 3.35
% 18.91/10.11  BG Simplification    : 0.15
% 18.91/10.11  Subsumption          : 2.25
% 18.91/10.11  Abstraction          : 0.25
% 18.91/10.11  MUC search           : 0.00
% 18.91/10.11  Cooper               : 0.00
% 18.91/10.11  Total                : 9.37
% 18.91/10.11  Index Insertion      : 0.00
% 18.91/10.11  Index Deletion       : 0.00
% 18.91/10.11  Index Matching       : 0.00
% 18.91/10.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
