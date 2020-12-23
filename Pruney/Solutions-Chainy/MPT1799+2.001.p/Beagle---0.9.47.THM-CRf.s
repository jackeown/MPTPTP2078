%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:57 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 391 expanded)
%              Number of leaves         :   30 ( 159 expanded)
%              Depth                    :   23
%              Number of atoms          :  250 (1762 expanded)
%              Number of equality atoms :   33 ( 200 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_pre_topc(C,k8_tmap_1(A,B))
               => ( u1_struct_0(C) = u1_struct_0(B)
                 => ( v1_tsep_1(C,k8_tmap_1(A,B))
                    & m1_pre_topc(C,k8_tmap_1(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_tmap_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
             => ( C = B
               => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v2_pre_topc(k8_tmap_1(A_5,B_6))
      | ~ m1_pre_topc(B_6,A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,
    ( ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    ~ v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( l1_pre_topc(k8_tmap_1(A_5,B_6))
      | ~ m1_pre_topc(B_6,A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_161,plain,(
    ! [A_53,B_54] :
      ( u1_struct_0(k8_tmap_1(A_53,B_54)) = u1_struct_0(A_53)
      | ~ m1_pre_topc(B_54,A_53)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    ! [B_33,A_31] :
      ( m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_618,plain,(
    ! [B_92,A_93,B_94] :
      ( m1_subset_1(u1_struct_0(B_92),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_pre_topc(B_92,k8_tmap_1(A_93,B_94))
      | ~ l1_pre_topc(k8_tmap_1(A_93,B_94))
      | ~ m1_pre_topc(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_28])).

tff(c_620,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_618])).

tff(c_623,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_620])).

tff(c_624,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_623])).

tff(c_625,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_628,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_625])).

tff(c_631,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_628])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_631])).

tff(c_635,plain,(
    l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_pre_topc(k8_tmap_1(A_5,B_6))
      | ~ m1_pre_topc(B_6,A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_526,plain,(
    ! [A_84,B_85] :
      ( k5_tmap_1(A_84,u1_struct_0(B_85)) = u1_pre_topc(k8_tmap_1(A_84,B_85))
      | ~ m1_subset_1(u1_struct_0(B_85),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_pre_topc(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_566,plain,(
    ! [A_86,B_87] :
      ( k5_tmap_1(A_86,u1_struct_0(B_87)) = u1_pre_topc(k8_tmap_1(A_86,B_87))
      | v2_struct_0(B_87)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86)
      | ~ m1_pre_topc(B_87,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_28,c_526])).

tff(c_591,plain,(
    ! [A_86] :
      ( k5_tmap_1(A_86,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_86,'#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86)
      | ~ m1_pre_topc('#skF_2',A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_566])).

tff(c_594,plain,(
    ! [A_86] :
      ( k5_tmap_1(A_86,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_86,'#skF_2'))
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86)
      | ~ m1_pre_topc('#skF_2',A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_591])).

tff(c_634,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( g1_pre_topc(u1_struct_0(A_2),k5_tmap_1(A_2,B_4)) = k6_tmap_1(A_2,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_659,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1',u1_struct_0('#skF_3'))) = k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_634,c_4])).

tff(c_668,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1',u1_struct_0('#skF_3'))) = k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_659])).

tff(c_669,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1',u1_struct_0('#skF_3'))) = k6_tmap_1('#skF_1',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_668])).

tff(c_830,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_669])).

tff(c_851,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_42,c_830])).

tff(c_852,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_851])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_53,B_54] :
      ( g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(k8_tmap_1(A_53,B_54))) = k8_tmap_1(A_53,B_54)
      | ~ v1_pre_topc(k8_tmap_1(A_53,B_54))
      | ~ l1_pre_topc(k8_tmap_1(A_53,B_54))
      | ~ m1_pre_topc(B_54,A_53)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_867,plain,
    ( k6_tmap_1('#skF_1',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_182])).

tff(c_874,plain,
    ( k6_tmap_1('#skF_1',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_635,c_867])).

tff(c_875,plain,
    ( k6_tmap_1('#skF_1',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_874])).

tff(c_880,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_883,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_880])).

tff(c_886,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_883])).

tff(c_888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_886])).

tff(c_889,plain,(
    k6_tmap_1('#skF_1',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( u1_struct_0(k6_tmap_1(A_7,B_9)) = u1_struct_0(A_7)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_665,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_634,c_14])).

tff(c_676,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_665])).

tff(c_677,plain,(
    u1_struct_0(k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_676])).

tff(c_16,plain,(
    ! [C_16,A_10] :
      ( v3_pre_topc(C_16,k6_tmap_1(A_10,C_16))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_10,C_16))))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_695,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),k6_tmap_1('#skF_1',u1_struct_0('#skF_3')))
    | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_16])).

tff(c_752,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),k6_tmap_1('#skF_1',u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_634,c_634,c_695])).

tff(c_753,plain,(
    v3_pre_topc(u1_struct_0('#skF_3'),k6_tmap_1('#skF_1',u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_752])).

tff(c_938,plain,(
    v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_753])).

tff(c_256,plain,(
    ! [B_60,A_61] :
      ( v1_tsep_1(B_60,A_61)
      | ~ v3_pre_topc(u1_struct_0(B_60),A_61)
      | ~ m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_288,plain,(
    ! [B_33,A_31] :
      ( v1_tsep_1(B_33,A_31)
      | ~ v3_pre_topc(u1_struct_0(B_33),A_31)
      | ~ v2_pre_topc(A_31)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_28,c_256])).

tff(c_990,plain,
    ( v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_938,c_288])).

tff(c_996,plain,
    ( v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_34,c_990])).

tff(c_997,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_996])).

tff(c_1000,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_997])).

tff(c_1003,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_1000])).

tff(c_1005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.60  
% 3.24/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.60  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.60  
% 3.24/1.60  %Foreground sorts:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Background operators:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Foreground operators:
% 3.24/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.24/1.60  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.24/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.60  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.24/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.60  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 3.24/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.24/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.60  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.24/1.60  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.24/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.24/1.60  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.24/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.60  
% 3.63/1.62  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_pre_topc(C, k8_tmap_1(A, B)) => ((u1_struct_0(C) = u1_struct_0(B)) => (v1_tsep_1(C, k8_tmap_1(A, B)) & m1_pre_topc(C, k8_tmap_1(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_tmap_1)).
% 3.63/1.62  tff(f_58, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 3.63/1.62  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 3.63/1.62  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.63/1.62  tff(f_43, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.63/1.62  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.63/1.62  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.63/1.62  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 3.63/1.62  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.63/1.62  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_8, plain, (![A_5, B_6]: (v2_pre_topc(k8_tmap_1(A_5, B_6)) | ~m1_pre_topc(B_6, A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.62  tff(c_34, plain, (m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_30, plain, (~m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_46, plain, (~v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 3.63/1.62  tff(c_6, plain, (![A_5, B_6]: (l1_pre_topc(k8_tmap_1(A_5, B_6)) | ~m1_pre_topc(B_6, A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.62  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_161, plain, (![A_53, B_54]: (u1_struct_0(k8_tmap_1(A_53, B_54))=u1_struct_0(A_53) | ~m1_pre_topc(B_54, A_53) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.63/1.62  tff(c_28, plain, (![B_33, A_31]: (m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.63/1.62  tff(c_618, plain, (![B_92, A_93, B_94]: (m1_subset_1(u1_struct_0(B_92), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_pre_topc(B_92, k8_tmap_1(A_93, B_94)) | ~l1_pre_topc(k8_tmap_1(A_93, B_94)) | ~m1_pre_topc(B_94, A_93) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(superposition, [status(thm), theory('equality')], [c_161, c_28])).
% 3.63/1.62  tff(c_620, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_618])).
% 3.63/1.62  tff(c_623, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_620])).
% 3.63/1.62  tff(c_624, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_623])).
% 3.63/1.62  tff(c_625, plain, (~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_624])).
% 3.63/1.62  tff(c_628, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_625])).
% 3.63/1.62  tff(c_631, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_628])).
% 3.63/1.62  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_631])).
% 3.63/1.62  tff(c_635, plain, (l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_624])).
% 3.63/1.62  tff(c_10, plain, (![A_5, B_6]: (v1_pre_topc(k8_tmap_1(A_5, B_6)) | ~m1_pre_topc(B_6, A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.62  tff(c_32, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.63/1.62  tff(c_526, plain, (![A_84, B_85]: (k5_tmap_1(A_84, u1_struct_0(B_85))=u1_pre_topc(k8_tmap_1(A_84, B_85)) | ~m1_subset_1(u1_struct_0(B_85), k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_pre_topc(B_85, A_84) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.63/1.62  tff(c_566, plain, (![A_86, B_87]: (k5_tmap_1(A_86, u1_struct_0(B_87))=u1_pre_topc(k8_tmap_1(A_86, B_87)) | v2_struct_0(B_87) | ~v2_pre_topc(A_86) | v2_struct_0(A_86) | ~m1_pre_topc(B_87, A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_28, c_526])).
% 3.63/1.62  tff(c_591, plain, (![A_86]: (k5_tmap_1(A_86, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_86, '#skF_2')) | v2_struct_0('#skF_2') | ~v2_pre_topc(A_86) | v2_struct_0(A_86) | ~m1_pre_topc('#skF_2', A_86) | ~l1_pre_topc(A_86))), inference(superposition, [status(thm), theory('equality')], [c_32, c_566])).
% 3.63/1.62  tff(c_594, plain, (![A_86]: (k5_tmap_1(A_86, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_86, '#skF_2')) | ~v2_pre_topc(A_86) | v2_struct_0(A_86) | ~m1_pre_topc('#skF_2', A_86) | ~l1_pre_topc(A_86))), inference(negUnitSimplification, [status(thm)], [c_38, c_591])).
% 3.63/1.62  tff(c_634, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_624])).
% 3.63/1.62  tff(c_4, plain, (![A_2, B_4]: (g1_pre_topc(u1_struct_0(A_2), k5_tmap_1(A_2, B_4))=k6_tmap_1(A_2, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2) | ~v2_pre_topc(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.63/1.62  tff(c_659, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', u1_struct_0('#skF_3')))=k6_tmap_1('#skF_1', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_634, c_4])).
% 3.63/1.62  tff(c_668, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', u1_struct_0('#skF_3')))=k6_tmap_1('#skF_1', u1_struct_0('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_659])).
% 3.63/1.62  tff(c_669, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', u1_struct_0('#skF_3')))=k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_668])).
% 3.63/1.62  tff(c_830, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_594, c_669])).
% 3.63/1.62  tff(c_851, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', u1_struct_0('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_42, c_830])).
% 3.63/1.62  tff(c_852, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_851])).
% 3.63/1.62  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.62  tff(c_182, plain, (![A_53, B_54]: (g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(k8_tmap_1(A_53, B_54)))=k8_tmap_1(A_53, B_54) | ~v1_pre_topc(k8_tmap_1(A_53, B_54)) | ~l1_pre_topc(k8_tmap_1(A_53, B_54)) | ~m1_pre_topc(B_54, A_53) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 3.63/1.62  tff(c_867, plain, (k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_852, c_182])).
% 3.63/1.62  tff(c_874, plain, (k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_635, c_867])).
% 3.63/1.62  tff(c_875, plain, (k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_874])).
% 3.63/1.62  tff(c_880, plain, (~v1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_875])).
% 3.63/1.62  tff(c_883, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_880])).
% 3.63/1.62  tff(c_886, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_883])).
% 3.63/1.62  tff(c_888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_886])).
% 3.63/1.62  tff(c_889, plain, (k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_875])).
% 3.63/1.62  tff(c_14, plain, (![A_7, B_9]: (u1_struct_0(k6_tmap_1(A_7, B_9))=u1_struct_0(A_7) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.63/1.62  tff(c_665, plain, (u1_struct_0(k6_tmap_1('#skF_1', u1_struct_0('#skF_3')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_634, c_14])).
% 3.63/1.62  tff(c_676, plain, (u1_struct_0(k6_tmap_1('#skF_1', u1_struct_0('#skF_3')))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_665])).
% 3.63/1.62  tff(c_677, plain, (u1_struct_0(k6_tmap_1('#skF_1', u1_struct_0('#skF_3')))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_676])).
% 3.63/1.62  tff(c_16, plain, (![C_16, A_10]: (v3_pre_topc(C_16, k6_tmap_1(A_10, C_16)) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_10, C_16)))) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.63/1.62  tff(c_695, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_677, c_16])).
% 3.63/1.62  tff(c_752, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k6_tmap_1('#skF_1', u1_struct_0('#skF_3'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_634, c_634, c_695])).
% 3.63/1.62  tff(c_753, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k6_tmap_1('#skF_1', u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_752])).
% 3.63/1.62  tff(c_938, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_753])).
% 3.63/1.62  tff(c_256, plain, (![B_60, A_61]: (v1_tsep_1(B_60, A_61) | ~v3_pre_topc(u1_struct_0(B_60), A_61) | ~m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.63/1.62  tff(c_288, plain, (![B_33, A_31]: (v1_tsep_1(B_33, A_31) | ~v3_pre_topc(u1_struct_0(B_33), A_31) | ~v2_pre_topc(A_31) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_28, c_256])).
% 3.63/1.62  tff(c_990, plain, (v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_938, c_288])).
% 3.63/1.62  tff(c_996, plain, (v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_34, c_990])).
% 3.63/1.62  tff(c_997, plain, (~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_996])).
% 3.63/1.62  tff(c_1000, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_997])).
% 3.63/1.62  tff(c_1003, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_1000])).
% 3.63/1.62  tff(c_1005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1003])).
% 3.63/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.62  
% 3.63/1.62  Inference rules
% 3.63/1.62  ----------------------
% 3.63/1.62  #Ref     : 0
% 3.63/1.62  #Sup     : 242
% 3.63/1.62  #Fact    : 0
% 3.63/1.62  #Define  : 0
% 3.63/1.62  #Split   : 3
% 3.63/1.62  #Chain   : 0
% 3.63/1.62  #Close   : 0
% 3.63/1.62  
% 3.63/1.62  Ordering : KBO
% 3.63/1.62  
% 3.63/1.62  Simplification rules
% 3.63/1.62  ----------------------
% 3.63/1.62  #Subsume      : 27
% 3.63/1.62  #Demod        : 126
% 3.63/1.62  #Tautology    : 57
% 3.63/1.62  #SimpNegUnit  : 42
% 3.63/1.62  #BackRed      : 5
% 3.63/1.62  
% 3.63/1.62  #Partial instantiations: 0
% 3.63/1.62  #Strategies tried      : 1
% 3.63/1.62  
% 3.63/1.62  Timing (in seconds)
% 3.63/1.62  ----------------------
% 3.63/1.62  Preprocessing        : 0.36
% 3.63/1.62  Parsing              : 0.19
% 3.63/1.62  CNF conversion       : 0.02
% 3.63/1.62  Main loop            : 0.44
% 3.63/1.63  Inferencing          : 0.15
% 3.63/1.63  Reduction            : 0.14
% 3.63/1.63  Demodulation         : 0.10
% 3.63/1.63  BG Simplification    : 0.03
% 3.63/1.63  Subsumption          : 0.09
% 3.63/1.63  Abstraction          : 0.02
% 3.63/1.63  MUC search           : 0.00
% 3.63/1.63  Cooper               : 0.00
% 3.63/1.63  Total                : 0.84
% 3.63/1.63  Index Insertion      : 0.00
% 3.63/1.63  Index Deletion       : 0.00
% 3.63/1.63  Index Matching       : 0.00
% 3.63/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
