%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1687+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:14 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 858 expanded)
%              Number of leaves         :   41 ( 295 expanded)
%              Depth                    :   14
%              Number of atoms          :  405 (3643 expanded)
%              Number of equality atoms :   66 ( 617 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v23_waybel_0 > v1_funct_2 > r1_orders_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_orders_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

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

tff(v23_waybel_0,type,(
    v23_waybel_0: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_orders_2(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v23_waybel_0(C,A,B)
                 => ( v1_funct_1(k2_funct_1(C))
                    & v1_funct_2(k2_funct_1(C),u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A))))
                    & k2_relat_1(k2_funct_1(C)) = u1_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_waybel_0)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_59,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_orders_2(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v23_waybel_0(C,A,B)
              <=> ( v2_funct_1(C)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = u1_struct_0(B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r1_orders_2(A,D,E)
                          <=> r1_orders_2(B,k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,D),k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,E)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_waybel_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_81,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_85,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_81])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_20,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != u1_struct_0('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_116,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_119,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68,c_119])).

tff(c_124,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | k2_relat_1(k2_funct_1('#skF_5')) != u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_189,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_192,plain,
    ( u1_struct_0('#skF_3') != k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_189])).

tff(c_194,plain,
    ( u1_struct_0('#skF_3') != k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68,c_192])).

tff(c_195,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_146,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_154,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_146])).

tff(c_199,plain,(
    ! [B_101,A_102,C_103] :
      ( k1_xboole_0 = B_101
      | k1_relset_1(A_102,B_101,C_103) = A_102
      | ~ v1_funct_2(C_103,A_102,B_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_205,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_199])).

tff(c_209,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154,c_205])).

tff(c_210,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_215,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_66])).

tff(c_62,plain,(
    v23_waybel_0('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_214,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_64])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_74,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_321,plain,(
    ! [C_110,A_111,B_112] :
      ( v2_funct_1(C_110)
      | ~ v23_waybel_0(C_110,A_111,B_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_110)
      | ~ l1_orders_2(B_112)
      | v2_struct_0(B_112)
      | ~ l1_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_324,plain,(
    ! [C_110,B_112] :
      ( v2_funct_1(C_110)
      | ~ v23_waybel_0(C_110,'#skF_3',B_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_110,u1_struct_0('#skF_3'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_110)
      | ~ l1_orders_2(B_112)
      | v2_struct_0(B_112)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_321])).

tff(c_329,plain,(
    ! [C_110,B_112] :
      ( v2_funct_1(C_110)
      | ~ v23_waybel_0(C_110,'#skF_3',B_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_110,k1_relat_1('#skF_5'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_110)
      | ~ l1_orders_2(B_112)
      | v2_struct_0(B_112)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_210,c_324])).

tff(c_449,plain,(
    ! [C_125,B_126] :
      ( v2_funct_1(C_125)
      | ~ v23_waybel_0(C_125,'#skF_3',B_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_126))))
      | ~ v1_funct_2(C_125,k1_relat_1('#skF_5'),u1_struct_0(B_126))
      | ~ v1_funct_1(C_125)
      | ~ l1_orders_2(B_126)
      | v2_struct_0(B_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_329])).

tff(c_452,plain,
    ( v2_funct_1('#skF_5')
    | ~ v23_waybel_0('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_214,c_449])).

tff(c_458,plain,
    ( v2_funct_1('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_215,c_62,c_452])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_195,c_458])).

tff(c_461,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_24,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_470,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_24])).

tff(c_474,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_470])).

tff(c_475,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_474])).

tff(c_479,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_475])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_479])).

tff(c_484,plain,(
    u1_struct_0('#skF_3') != k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_489,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_495,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_489])).

tff(c_499,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154,c_495])).

tff(c_500,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_499])).

tff(c_508,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_24])).

tff(c_512,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_508])).

tff(c_513,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_512])).

tff(c_517,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_513])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_517])).

tff(c_523,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_536,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_36])).

tff(c_552,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68,c_536])).

tff(c_558,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_638,plain,(
    ! [B_147,A_148,C_149] :
      ( k1_xboole_0 = B_147
      | k1_relset_1(A_148,B_147,C_149) = A_148
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_647,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_638])).

tff(c_654,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_154,c_647])).

tff(c_655,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_665,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_66])).

tff(c_664,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_64])).

tff(c_768,plain,(
    ! [C_153,A_154,B_155] :
      ( v2_funct_1(C_153)
      | ~ v23_waybel_0(C_153,A_154,B_155)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_154),u1_struct_0(B_155))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_154),u1_struct_0(B_155))
      | ~ v1_funct_1(C_153)
      | ~ l1_orders_2(B_155)
      | v2_struct_0(B_155)
      | ~ l1_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_771,plain,(
    ! [C_153,B_155] :
      ( v2_funct_1(C_153)
      | ~ v23_waybel_0(C_153,'#skF_3',B_155)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_155))))
      | ~ v1_funct_2(C_153,u1_struct_0('#skF_3'),u1_struct_0(B_155))
      | ~ v1_funct_1(C_153)
      | ~ l1_orders_2(B_155)
      | v2_struct_0(B_155)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_768])).

tff(c_776,plain,(
    ! [C_153,B_155] :
      ( v2_funct_1(C_153)
      | ~ v23_waybel_0(C_153,'#skF_3',B_155)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_155))))
      | ~ v1_funct_2(C_153,k1_relat_1('#skF_5'),u1_struct_0(B_155))
      | ~ v1_funct_1(C_153)
      | ~ l1_orders_2(B_155)
      | v2_struct_0(B_155)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_655,c_771])).

tff(c_784,plain,(
    ! [C_156,B_157] :
      ( v2_funct_1(C_156)
      | ~ v23_waybel_0(C_156,'#skF_3',B_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_156,k1_relat_1('#skF_5'),u1_struct_0(B_157))
      | ~ v1_funct_1(C_156)
      | ~ l1_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_776])).

tff(c_787,plain,
    ( v2_funct_1('#skF_5')
    | ~ v23_waybel_0('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_664,c_784])).

tff(c_793,plain,
    ( v2_funct_1('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_665,c_62,c_787])).

tff(c_795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_558,c_793])).

tff(c_796,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_806,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_24])).

tff(c_810,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_806])).

tff(c_811,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_810])).

tff(c_815,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_811])).

tff(c_819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_815])).

tff(c_821,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_38,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_820,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_125,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_funct_2(A_16,k1_relat_1(A_16),k2_relat_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_539,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_32])).

tff(c_554,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),u1_struct_0('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_539])).

tff(c_908,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),k1_relat_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_554])).

tff(c_909,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_914,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_909])).

tff(c_918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68,c_914])).

tff(c_920,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_30,plain,(
    ! [A_16] :
      ( m1_subset_1(A_16,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_16),k2_relat_1(A_16))))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_533,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),u1_struct_0('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_30])).

tff(c_550,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),u1_struct_0('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_533])).

tff(c_930,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_820,c_550])).

tff(c_942,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_930])).

tff(c_949,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68,c_821,c_942])).

tff(c_826,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_66])).

tff(c_111,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_115,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_111])).

tff(c_824,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_115])).

tff(c_825,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_64])).

tff(c_1722,plain,(
    ! [A_217,B_218,C_219] :
      ( k2_relset_1(u1_struct_0(A_217),u1_struct_0(B_218),C_219) = u1_struct_0(B_218)
      | ~ v23_waybel_0(C_219,A_217,B_218)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217),u1_struct_0(B_218))))
      | ~ v1_funct_2(C_219,u1_struct_0(A_217),u1_struct_0(B_218))
      | ~ v1_funct_1(C_219)
      | ~ l1_orders_2(B_218)
      | v2_struct_0(B_218)
      | ~ l1_orders_2(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1725,plain,(
    ! [B_218,C_219] :
      ( k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_218),C_219) = u1_struct_0(B_218)
      | ~ v23_waybel_0(C_219,'#skF_3',B_218)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_218))))
      | ~ v1_funct_2(C_219,u1_struct_0('#skF_3'),u1_struct_0(B_218))
      | ~ v1_funct_1(C_219)
      | ~ l1_orders_2(B_218)
      | v2_struct_0(B_218)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_1722])).

tff(c_1730,plain,(
    ! [B_218,C_219] :
      ( k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_218),C_219) = u1_struct_0(B_218)
      | ~ v23_waybel_0(C_219,'#skF_3',B_218)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_218))))
      | ~ v1_funct_2(C_219,k1_relat_1('#skF_5'),u1_struct_0(B_218))
      | ~ v1_funct_1(C_219)
      | ~ l1_orders_2(B_218)
      | v2_struct_0(B_218)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_820,c_820,c_1725])).

tff(c_1928,plain,(
    ! [B_232,C_233] :
      ( k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_232),C_233) = u1_struct_0(B_232)
      | ~ v23_waybel_0(C_233,'#skF_3',B_232)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_232))))
      | ~ v1_funct_2(C_233,k1_relat_1('#skF_5'),u1_struct_0(B_232))
      | ~ v1_funct_1(C_233)
      | ~ l1_orders_2(B_232)
      | v2_struct_0(B_232) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1730])).

tff(c_1931,plain,
    ( k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_4')
    | ~ v23_waybel_0('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_825,c_1928])).

tff(c_1937,plain,
    ( u1_struct_0('#skF_4') = k2_relat_1('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_826,c_62,c_824,c_1931])).

tff(c_1938,plain,(
    u1_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1937])).

tff(c_919,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_923,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_919])).

tff(c_925,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68,c_821,c_923])).

tff(c_1234,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(u1_struct_0(A_179),u1_struct_0(B_180),C_181) = u1_struct_0(B_180)
      | ~ v23_waybel_0(C_181,A_179,B_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_181,u1_struct_0(A_179),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ l1_orders_2(B_180)
      | v2_struct_0(B_180)
      | ~ l1_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1237,plain,(
    ! [B_180,C_181] :
      ( k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_180),C_181) = u1_struct_0(B_180)
      | ~ v23_waybel_0(C_181,'#skF_3',B_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_181,u1_struct_0('#skF_3'),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ l1_orders_2(B_180)
      | v2_struct_0(B_180)
      | ~ l1_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_1234])).

tff(c_1242,plain,(
    ! [B_180,C_181] :
      ( k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_180),C_181) = u1_struct_0(B_180)
      | ~ v23_waybel_0(C_181,'#skF_3',B_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_181,k1_relat_1('#skF_5'),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ l1_orders_2(B_180)
      | v2_struct_0(B_180)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_820,c_820,c_1237])).

tff(c_1509,plain,(
    ! [B_202,C_203] :
      ( k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_202),C_203) = u1_struct_0(B_202)
      | ~ v23_waybel_0(C_203,'#skF_3',B_202)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_202))))
      | ~ v1_funct_2(C_203,k1_relat_1('#skF_5'),u1_struct_0(B_202))
      | ~ v1_funct_1(C_203)
      | ~ l1_orders_2(B_202)
      | v2_struct_0(B_202) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1242])).

tff(c_1512,plain,
    ( k2_relset_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'),'#skF_5') = u1_struct_0('#skF_4')
    | ~ v23_waybel_0('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_825,c_1509])).

tff(c_1518,plain,
    ( u1_struct_0('#skF_4') = k2_relat_1('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_826,c_62,c_824,c_1512])).

tff(c_1519,plain,(
    u1_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1518])).

tff(c_522,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_968,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k1_relat_1('#skF_5'))))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),u1_struct_0('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_820,c_522])).

tff(c_969,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),u1_struct_0('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_1523,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_969])).

tff(c_1530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_1523])).

tff(c_1531,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k1_relat_1('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_1942,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1531])).

tff(c_1950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_1942])).

%------------------------------------------------------------------------------
