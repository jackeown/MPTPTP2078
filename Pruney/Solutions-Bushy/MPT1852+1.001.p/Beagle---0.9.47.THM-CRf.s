%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1852+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 271 expanded)
%              Number of leaves         :   19 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :   92 ( 690 expanded)
%              Number of equality atoms :   21 ( 236 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_16,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),u1_pre_topc(A_1))
      | v3_tdlat_3(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | v3_tdlat_3(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_5] :
      ( m1_subset_1(u1_pre_topc(A_5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_5))))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37,plain,(
    ! [C_17,A_18,D_19,B_20] :
      ( C_17 = A_18
      | g1_pre_topc(C_17,D_19) != g1_pre_topc(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [A_25,B_26] :
      ( u1_struct_0('#skF_2') = A_25
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_37])).

tff(c_55,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_63,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_55])).

tff(c_65,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_86,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_10])).

tff(c_94,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_86])).

tff(c_76,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_20])).

tff(c_12,plain,(
    ! [D_11,B_7,C_10,A_6] :
      ( D_11 = B_7
      | g1_pre_topc(C_10,D_11) != g1_pre_topc(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    ! [D_11,C_10] :
      ( u1_pre_topc('#skF_2') = D_11
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_10,D_11)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_124,plain,(
    ! [D_11,C_10] :
      ( u1_pre_topc('#skF_2') = D_11
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_10,D_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_116])).

tff(c_130,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_18,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_30),B_31),u1_pre_topc(A_30))
      | ~ r2_hidden(B_31,u1_pre_topc(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v3_tdlat_3(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_31] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_31),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_31,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_96])).

tff(c_106,plain,(
    ! [B_31] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_31),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_31,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_65,c_103])).

tff(c_181,plain,(
    ! [B_38] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_38),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_38,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_106])).

tff(c_4,plain,(
    ! [A_1] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_1),'#skF_1'(A_1)),u1_pre_topc(A_1))
      | v3_tdlat_3(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_185,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_188,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_189,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_188])).

tff(c_190,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_193,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_196,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_196])).

tff(c_199,plain,(
    ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_203,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_206,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_203])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_206])).

%------------------------------------------------------------------------------
