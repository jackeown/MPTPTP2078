%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:19 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  160 (5374 expanded)
%              Number of leaves         :   47 (1914 expanded)
%              Depth                    :   18
%              Number of atoms          :  272 (16713 expanded)
%              Number of equality atoms :  115 (6261 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_29,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_31,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_27,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_117,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_68,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_72,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_106,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_114,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_106])).

tff(c_113,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_106])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_128,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_113,c_62])).

tff(c_130,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_130])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_580,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_584,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_580])).

tff(c_60,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_140,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_113,c_60])).

tff(c_585,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_140])).

tff(c_8,plain,(
    ! [A_4] : ~ v1_xboole_0(k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [A_1] : k3_tarski(k1_zfmisc_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_1'(A_53),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_156,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_150])).

tff(c_160,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_156])).

tff(c_161,plain,(
    m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_160])).

tff(c_145,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    ! [A_23,B_26] :
      ( k3_tarski(A_23) != k1_xboole_0
      | ~ r2_hidden(B_26,A_23)
      | k1_xboole_0 = B_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_534,plain,(
    ! [B_102,A_103] :
      ( k3_tarski(B_102) != k1_xboole_0
      | k1_xboole_0 = A_103
      | v1_xboole_0(B_102)
      | ~ m1_subset_1(A_103,B_102) ) ),
    inference(resolution,[status(thm)],[c_145,c_42])).

tff(c_537,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4'))) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_161,c_534])).

tff(c_545,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_537])).

tff(c_546,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_545])).

tff(c_553,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_593,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_553])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_115,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64])).

tff(c_126,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_115])).

tff(c_596,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_126])).

tff(c_595,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_128])).

tff(c_640,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_644,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_595,c_640])).

tff(c_671,plain,(
    ! [B_126,A_127,C_128] :
      ( k1_xboole_0 = B_126
      | k1_relset_1(A_127,B_126,C_128) = A_127
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_674,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_595,c_671])).

tff(c_677,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_644,c_674])).

tff(c_678,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_677])).

tff(c_692,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_596])).

tff(c_590,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_584])).

tff(c_689,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_590])).

tff(c_690,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_595])).

tff(c_828,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_tops_2(A_138,B_139,C_140) = k2_funct_1(C_140)
      | ~ v2_funct_1(C_140)
      | k2_relset_1(A_138,B_139,C_140) != B_139
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_2(C_140,A_138,B_139)
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_834,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_690,c_828])).

tff(c_838,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_692,c_689,c_58,c_834])).

tff(c_759,plain,(
    ! [A_132,B_133,C_134] :
      ( m1_subset_1(k2_tops_2(A_132,B_133,C_134),k1_zfmisc_1(k2_zfmisc_1(B_133,A_132)))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_2(C_134,A_132,B_133)
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_928,plain,(
    ! [B_141,A_142,C_143] :
      ( k2_relset_1(B_141,A_142,k2_tops_2(A_142,B_141,C_143)) = k2_relat_1(k2_tops_2(A_142,B_141,C_143))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ v1_funct_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_759,c_20])).

tff(c_934,plain,
    ( k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) = k2_relat_1(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_690,c_928])).

tff(c_941,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_692,c_838,c_838,c_934])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_211,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_215,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_211])).

tff(c_216,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_140])).

tff(c_165,plain,(
    ! [B_54,A_55] :
      ( k3_tarski(B_54) != k1_xboole_0
      | k1_xboole_0 = A_55
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_145,c_42])).

tff(c_168,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4'))) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_161,c_165])).

tff(c_176,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_177,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_176])).

tff(c_184,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_224,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_184])).

tff(c_227,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_126])).

tff(c_226,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_128])).

tff(c_271,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_226,c_271])).

tff(c_290,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_293,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_226,c_290])).

tff(c_296,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_275,c_293])).

tff(c_297,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_296])).

tff(c_304,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_227])).

tff(c_221,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_215])).

tff(c_302,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_221])).

tff(c_301,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_226])).

tff(c_474,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_tops_2(A_99,B_100,C_101) = k2_funct_1(C_101)
      | ~ v2_funct_1(C_101)
      | k2_relset_1(A_99,B_100,C_101) != B_100
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_101,A_99,B_100)
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_480,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_301,c_474])).

tff(c_484,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_304,c_302,c_58,c_480])).

tff(c_375,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1(k2_tops_2(A_84,B_85,C_86),k1_zfmisc_1(k2_zfmisc_1(B_85,A_84)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_2(C_86,A_84,B_85)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_460,plain,(
    ! [B_96,A_97,C_98] :
      ( k1_relset_1(B_96,A_97,k2_tops_2(A_97,B_96,C_98)) = k1_relat_1(k2_tops_2(A_97,B_96,C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ v1_funct_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_375,c_18])).

tff(c_464,plain,
    ( k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) = k1_relat_1(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_301,c_460])).

tff(c_468,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) = k1_relat_1(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_304,c_464])).

tff(c_56,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_163,plain,
    ( k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_114,c_113,c_113,c_114,c_114,c_113,c_113,c_56])).

tff(c_164,plain,(
    k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_222,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_216,c_164])).

tff(c_299,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_297,c_222])).

tff(c_469,plain,(
    k1_relat_1(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_299])).

tff(c_499,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_469])).

tff(c_502,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_499])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_66,c_58,c_502])).

tff(c_507,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_38,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_1'(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_519,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_38])).

tff(c_529,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_73,c_519])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_529])).

tff(c_532,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_591,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_585,c_532])).

tff(c_686,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_678,c_678,c_591])).

tff(c_841,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_686])).

tff(c_943,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_841])).

tff(c_950,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_943])).

tff(c_954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_66,c_58,c_950])).

tff(c_955,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_967,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_38])).

tff(c_977,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_73,c_967])).

tff(c_979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:23:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.57  
% 3.52/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.57  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.52/1.57  
% 3.52/1.57  %Foreground sorts:
% 3.52/1.57  
% 3.52/1.57  
% 3.52/1.57  %Background operators:
% 3.52/1.57  
% 3.52/1.57  
% 3.52/1.57  %Foreground operators:
% 3.52/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.57  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.52/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.52/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.57  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.52/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.57  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.52/1.57  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.52/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.52/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.57  
% 3.52/1.60  tff(f_165, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.52/1.60  tff(f_29, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.52/1.60  tff(f_31, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 3.52/1.60  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.52/1.60  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.52/1.60  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.52/1.60  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.52/1.60  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.52/1.60  tff(f_27, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.52/1.60  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc20_struct_0)).
% 3.52/1.60  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.52/1.60  tff(f_117, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 3.52/1.60  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.52/1.60  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.52/1.60  tff(f_129, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.52/1.60  tff(f_141, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.52/1.60  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_68, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.60  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.60  tff(c_73, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 3.52/1.60  tff(c_72, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_106, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.60  tff(c_114, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_106])).
% 3.52/1.60  tff(c_113, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_106])).
% 3.52/1.60  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_128, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_113, c_62])).
% 3.52/1.60  tff(c_130, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.52/1.60  tff(c_134, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_130])).
% 3.52/1.60  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_58, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_12, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.60  tff(c_580, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.60  tff(c_584, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_580])).
% 3.52/1.60  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_140, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_113, c_60])).
% 3.52/1.60  tff(c_585, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_584, c_140])).
% 3.52/1.60  tff(c_8, plain, (![A_4]: (~v1_xboole_0(k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.60  tff(c_2, plain, (![A_1]: (k3_tarski(k1_zfmisc_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.60  tff(c_150, plain, (![A_53]: (m1_subset_1('#skF_1'(A_53), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.52/1.60  tff(c_156, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_113, c_150])).
% 3.52/1.60  tff(c_160, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_156])).
% 3.52/1.60  tff(c_161, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_160])).
% 3.52/1.60  tff(c_145, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.60  tff(c_42, plain, (![A_23, B_26]: (k3_tarski(A_23)!=k1_xboole_0 | ~r2_hidden(B_26, A_23) | k1_xboole_0=B_26)), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.52/1.60  tff(c_534, plain, (![B_102, A_103]: (k3_tarski(B_102)!=k1_xboole_0 | k1_xboole_0=A_103 | v1_xboole_0(B_102) | ~m1_subset_1(A_103, B_102))), inference(resolution, [status(thm)], [c_145, c_42])).
% 3.52/1.60  tff(c_537, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4')))!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_161, c_534])).
% 3.52/1.60  tff(c_545, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_537])).
% 3.52/1.60  tff(c_546, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8, c_545])).
% 3.52/1.60  tff(c_553, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_546])).
% 3.52/1.60  tff(c_593, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_585, c_553])).
% 3.52/1.60  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_115, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64])).
% 3.52/1.60  tff(c_126, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_115])).
% 3.52/1.60  tff(c_596, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_126])).
% 3.52/1.60  tff(c_595, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_128])).
% 3.52/1.60  tff(c_640, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.52/1.60  tff(c_644, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_595, c_640])).
% 3.52/1.60  tff(c_671, plain, (![B_126, A_127, C_128]: (k1_xboole_0=B_126 | k1_relset_1(A_127, B_126, C_128)=A_127 | ~v1_funct_2(C_128, A_127, B_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.52/1.60  tff(c_674, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_595, c_671])).
% 3.52/1.60  tff(c_677, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_644, c_674])).
% 3.52/1.60  tff(c_678, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_593, c_677])).
% 3.52/1.60  tff(c_692, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_678, c_596])).
% 3.52/1.60  tff(c_590, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_584])).
% 3.52/1.60  tff(c_689, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_590])).
% 3.52/1.60  tff(c_690, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_678, c_595])).
% 3.52/1.60  tff(c_828, plain, (![A_138, B_139, C_140]: (k2_tops_2(A_138, B_139, C_140)=k2_funct_1(C_140) | ~v2_funct_1(C_140) | k2_relset_1(A_138, B_139, C_140)!=B_139 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_2(C_140, A_138, B_139) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.52/1.60  tff(c_834, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_690, c_828])).
% 3.52/1.60  tff(c_838, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_692, c_689, c_58, c_834])).
% 3.52/1.60  tff(c_759, plain, (![A_132, B_133, C_134]: (m1_subset_1(k2_tops_2(A_132, B_133, C_134), k1_zfmisc_1(k2_zfmisc_1(B_133, A_132))) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_2(C_134, A_132, B_133) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.52/1.60  tff(c_20, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.60  tff(c_928, plain, (![B_141, A_142, C_143]: (k2_relset_1(B_141, A_142, k2_tops_2(A_142, B_141, C_143))=k2_relat_1(k2_tops_2(A_142, B_141, C_143)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_2(C_143, A_142, B_141) | ~v1_funct_1(C_143))), inference(resolution, [status(thm)], [c_759, c_20])).
% 3.52/1.60  tff(c_934, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))=k2_relat_1(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_690, c_928])).
% 3.52/1.60  tff(c_941, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_692, c_838, c_838, c_934])).
% 3.52/1.60  tff(c_14, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.60  tff(c_211, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.60  tff(c_215, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_211])).
% 3.52/1.60  tff(c_216, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_140])).
% 3.52/1.60  tff(c_165, plain, (![B_54, A_55]: (k3_tarski(B_54)!=k1_xboole_0 | k1_xboole_0=A_55 | v1_xboole_0(B_54) | ~m1_subset_1(A_55, B_54))), inference(resolution, [status(thm)], [c_145, c_42])).
% 3.52/1.60  tff(c_168, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4')))!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_161, c_165])).
% 3.52/1.60  tff(c_176, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_168])).
% 3.52/1.60  tff(c_177, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8, c_176])).
% 3.52/1.60  tff(c_184, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_177])).
% 3.52/1.60  tff(c_224, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_216, c_184])).
% 3.52/1.60  tff(c_227, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_126])).
% 3.52/1.60  tff(c_226, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_128])).
% 3.52/1.60  tff(c_271, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.52/1.60  tff(c_275, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_226, c_271])).
% 3.52/1.60  tff(c_290, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.52/1.60  tff(c_293, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_226, c_290])).
% 3.52/1.60  tff(c_296, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_275, c_293])).
% 3.52/1.60  tff(c_297, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_224, c_296])).
% 3.52/1.60  tff(c_304, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_227])).
% 3.52/1.60  tff(c_221, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_215])).
% 3.52/1.60  tff(c_302, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_221])).
% 3.52/1.60  tff(c_301, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_226])).
% 3.52/1.60  tff(c_474, plain, (![A_99, B_100, C_101]: (k2_tops_2(A_99, B_100, C_101)=k2_funct_1(C_101) | ~v2_funct_1(C_101) | k2_relset_1(A_99, B_100, C_101)!=B_100 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_101, A_99, B_100) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.52/1.60  tff(c_480, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_301, c_474])).
% 3.52/1.60  tff(c_484, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_304, c_302, c_58, c_480])).
% 3.52/1.60  tff(c_375, plain, (![A_84, B_85, C_86]: (m1_subset_1(k2_tops_2(A_84, B_85, C_86), k1_zfmisc_1(k2_zfmisc_1(B_85, A_84))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_2(C_86, A_84, B_85) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.52/1.60  tff(c_18, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.52/1.60  tff(c_460, plain, (![B_96, A_97, C_98]: (k1_relset_1(B_96, A_97, k2_tops_2(A_97, B_96, C_98))=k1_relat_1(k2_tops_2(A_97, B_96, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_98, A_97, B_96) | ~v1_funct_1(C_98))), inference(resolution, [status(thm)], [c_375, c_18])).
% 3.52/1.60  tff(c_464, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))=k1_relat_1(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_301, c_460])).
% 3.52/1.60  tff(c_468, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))=k1_relat_1(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_304, c_464])).
% 3.52/1.60  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.52/1.60  tff(c_163, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_114, c_113, c_113, c_114, c_114, c_113, c_113, c_56])).
% 3.52/1.60  tff(c_164, plain, (k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_163])).
% 3.52/1.60  tff(c_222, plain, (k1_relset_1(k2_relat_1('#skF_5'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_216, c_164])).
% 3.52/1.60  tff(c_299, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_297, c_222])).
% 3.52/1.60  tff(c_469, plain, (k1_relat_1(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_299])).
% 3.52/1.60  tff(c_499, plain, (k1_relat_1(k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_469])).
% 3.52/1.60  tff(c_502, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14, c_499])).
% 3.52/1.60  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_66, c_58, c_502])).
% 3.52/1.60  tff(c_507, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_177])).
% 3.52/1.60  tff(c_38, plain, (![A_21]: (~v1_xboole_0('#skF_1'(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.52/1.60  tff(c_519, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_507, c_38])).
% 3.52/1.60  tff(c_529, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_73, c_519])).
% 3.52/1.60  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_529])).
% 3.52/1.60  tff(c_532, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_163])).
% 3.52/1.60  tff(c_591, plain, (k2_relset_1(k2_relat_1('#skF_5'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_585, c_532])).
% 3.52/1.60  tff(c_686, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_678, c_678, c_591])).
% 3.52/1.60  tff(c_841, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_838, c_686])).
% 3.52/1.60  tff(c_943, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_941, c_841])).
% 3.52/1.60  tff(c_950, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12, c_943])).
% 3.52/1.60  tff(c_954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_66, c_58, c_950])).
% 3.52/1.60  tff(c_955, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_546])).
% 3.52/1.60  tff(c_967, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_955, c_38])).
% 3.52/1.60  tff(c_977, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_73, c_967])).
% 3.52/1.60  tff(c_979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_977])).
% 3.52/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.60  
% 3.52/1.60  Inference rules
% 3.52/1.60  ----------------------
% 3.52/1.60  #Ref     : 0
% 3.52/1.60  #Sup     : 194
% 3.52/1.60  #Fact    : 0
% 3.52/1.60  #Define  : 0
% 3.52/1.60  #Split   : 8
% 3.52/1.60  #Chain   : 0
% 3.52/1.60  #Close   : 0
% 3.52/1.60  
% 3.52/1.60  Ordering : KBO
% 3.52/1.60  
% 3.52/1.60  Simplification rules
% 3.52/1.60  ----------------------
% 3.52/1.60  #Subsume      : 14
% 3.52/1.60  #Demod        : 213
% 3.52/1.60  #Tautology    : 104
% 3.52/1.60  #SimpNegUnit  : 31
% 3.52/1.60  #BackRed      : 50
% 3.52/1.60  
% 3.52/1.60  #Partial instantiations: 0
% 3.52/1.60  #Strategies tried      : 1
% 3.52/1.60  
% 3.52/1.60  Timing (in seconds)
% 3.52/1.60  ----------------------
% 3.52/1.60  Preprocessing        : 0.37
% 3.52/1.61  Parsing              : 0.19
% 3.52/1.61  CNF conversion       : 0.03
% 3.52/1.61  Main loop            : 0.44
% 3.52/1.61  Inferencing          : 0.15
% 3.52/1.61  Reduction            : 0.15
% 3.52/1.61  Demodulation         : 0.11
% 3.52/1.61  BG Simplification    : 0.02
% 3.52/1.61  Subsumption          : 0.07
% 3.52/1.61  Abstraction          : 0.02
% 3.52/1.61  MUC search           : 0.00
% 3.52/1.61  Cooper               : 0.00
% 3.52/1.61  Total                : 0.87
% 3.52/1.61  Index Insertion      : 0.00
% 3.52/1.61  Index Deletion       : 0.00
% 3.52/1.61  Index Matching       : 0.00
% 3.52/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
