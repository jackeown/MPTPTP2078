%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1790+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:24 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 274 expanded)
%              Number of leaves         :   27 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  147 ( 854 expanded)
%              Number of equality atoms :   31 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
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

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_37,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_174,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,k5_tmap_1(A_49,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_178,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_174])).

tff(c_184,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_178])).

tff(c_185,plain,(
    r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_184])).

tff(c_204,plain,(
    ! [A_56,B_57] :
      ( g1_pre_topc(u1_struct_0(A_56),k5_tmap_1(A_56,B_57)) = k6_tmap_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_208,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_3')) = k6_tmap_1('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_204])).

tff(c_214,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_3')) = k6_tmap_1('#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_208])).

tff(c_215,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_3')) = k6_tmap_1('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_214])).

tff(c_24,plain,(
    ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_39,plain,(
    ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_72,plain,(
    ! [B_34,A_35] :
      ( v3_pre_topc(B_34,A_35)
      | ~ r2_hidden(B_34,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_72])).

tff(c_81,plain,
    ( ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_75])).

tff(c_86,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_99,plain,(
    ! [A_38,B_39] :
      ( l1_pre_topc(k6_tmap_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_99])).

tff(c_109,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_105])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_86,c_109])).

tff(c_113,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_143,plain,(
    ! [A_44,B_45] :
      ( v1_pre_topc(k6_tmap_1(A_44,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_149,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_143])).

tff(c_155,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_149])).

tff(c_156,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_155])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_16,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_pre_topc(A_10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [C_15,A_11,D_16,B_12] :
      ( C_15 = A_11
      | g1_pre_topc(C_15,D_16) != g1_pre_topc(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_232,plain,(
    ! [A_58,B_59] :
      ( u1_struct_0('#skF_1') = A_58
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_20])).

tff(c_237,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = u1_struct_0('#skF_1')
      | g1_pre_topc(u1_struct_0(A_60),u1_pre_topc(A_60)) != k6_tmap_1('#skF_1','#skF_3')
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_247,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = u1_struct_0('#skF_1')
      | k6_tmap_1('#skF_1','#skF_3') != A_63
      | ~ l1_pre_topc(A_63)
      | ~ v1_pre_topc(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_237])).

tff(c_250,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_3')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_156,c_247])).

tff(c_253,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_3')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_250])).

tff(c_284,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_16])).

tff(c_306,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_284])).

tff(c_281,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) = k6_tmap_1('#skF_1','#skF_3')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_2])).

tff(c_304,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) = k6_tmap_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_156,c_281])).

tff(c_18,plain,(
    ! [D_16,B_12,C_15,A_11] :
      ( D_16 = B_12
      | g1_pre_topc(C_15,D_16) != g1_pre_topc(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_325,plain,(
    ! [D_16,C_15] :
      ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = D_16
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(C_15,D_16)
      | ~ m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_18])).

tff(c_368,plain,(
    ! [D_69,C_70] :
      ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = D_69
      | k6_tmap_1('#skF_1','#skF_3') != g1_pre_topc(C_70,D_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_325])).

tff(c_377,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = k5_tmap_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_368])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_381,plain,(
    ~ r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_112])).

tff(c_385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_381])).

%------------------------------------------------------------------------------
