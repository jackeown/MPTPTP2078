%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1135+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 196 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 491 expanded)
%              Number of equality atoms :   19 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))
               => ( B = C
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(A,B)),u1_pre_topc(k1_pre_topc(A,B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_33,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_87,plain,(
    ! [A_36,B_37] :
      ( m1_pre_topc(k1_pre_topc(A_36,B_37),A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_87])).

tff(c_95,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_105,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( m1_pre_topc(A_17,g1_pre_topc(u1_struct_0(B_19),u1_pre_topc(B_19)))
      | ~ m1_pre_topc(A_17,B_19)
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( v1_pre_topc(k1_pre_topc(A_34,B_35))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_76])).

tff(c_86,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_53,plain,(
    ! [A_33] :
      ( g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)) = A_33
      | ~ v1_pre_topc(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_24])).

tff(c_62,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_34])).

tff(c_145,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_86,c_62])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_41,plain,(
    ! [A_27,B_28] :
      ( l1_pre_topc(g1_pre_topc(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    ! [A_16] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_118,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_124,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_118])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124])).

tff(c_132,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_152,plain,(
    ! [A_44,B_45] :
      ( k2_struct_0(k1_pre_topc(A_44,B_45)) = B_45
      | ~ m1_pre_topc(k1_pre_topc(A_44,B_45),A_44)
      | ~ v1_pre_topc(k1_pre_topc(A_44,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_152])).

tff(c_161,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_33,c_86,c_157])).

tff(c_4,plain,(
    ! [A_2,C_8] :
      ( k1_pre_topc(A_2,k2_struct_0(C_8)) = C_8
      | ~ m1_pre_topc(C_8,A_2)
      | ~ v1_pre_topc(C_8)
      | ~ m1_subset_1(k2_struct_0(C_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_4])).

tff(c_171,plain,(
    ! [A_46] :
      ( k1_pre_topc(A_46,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_46)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_161,c_165])).

tff(c_174,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_180,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_174])).

tff(c_181,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_180])).

tff(c_236,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_181])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_32,c_95,c_236])).

%------------------------------------------------------------------------------
