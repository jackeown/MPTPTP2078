%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 346 expanded)
%              Number of leaves         :   31 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  214 (1096 expanded)
%              Number of equality atoms :   25 ( 169 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_71,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_72,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_273,plain,(
    ! [A_82,B_83] :
      ( u1_pre_topc(k6_tmap_1(A_82,B_83)) = k5_tmap_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_285,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_273])).

tff(c_292,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_285])).

tff(c_293,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_292])).

tff(c_106,plain,(
    ! [A_54,B_55] :
      ( l1_pre_topc(k6_tmap_1(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_112,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_106])).

tff(c_116,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_112])).

tff(c_117,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_116])).

tff(c_168,plain,(
    ! [A_75,B_76] :
      ( u1_struct_0(k6_tmap_1(A_75,B_76)) = u1_struct_0(A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_174,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_168])).

tff(c_178,plain,
    ( u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_174])).

tff(c_179,plain,(
    u1_struct_0(k6_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_178])).

tff(c_8,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_8])).

tff(c_225,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_205])).

tff(c_295,plain,(
    m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_225])).

tff(c_14,plain,(
    ! [A_8,B_14] :
      ( r2_hidden('#skF_1'(A_8,B_14),B_14)
      | v1_tops_2(B_14,A_8)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_341,plain,
    ( r2_hidden('#skF_1'('#skF_2',k5_tmap_1('#skF_2','#skF_3')),k5_tmap_1('#skF_2','#skF_3'))
    | v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_295,c_14])).

tff(c_346,plain,
    ( r2_hidden('#skF_1'('#skF_2',k5_tmap_1('#skF_2','#skF_3')),k5_tmap_1('#skF_2','#skF_3'))
    | v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_341])).

tff(c_566,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_150,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,k5_tmap_1(A_71,B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_154,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_158,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_154])).

tff(c_159,plain,(
    r2_hidden('#skF_3',k5_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_158])).

tff(c_810,plain,(
    ! [C_117,A_118,B_119] :
      ( v3_pre_topc(C_117,A_118)
      | ~ r2_hidden(C_117,B_119)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ v1_tops_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_118))))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_975,plain,(
    ! [A_144] :
      ( v3_pre_topc('#skF_3',A_144)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),A_144)
      | ~ m1_subset_1(k5_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_144))))
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_159,c_810])).

tff(c_978,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_295,c_975])).

tff(c_984,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_566,c_46,c_978])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_984])).

tff(c_988,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_18,plain,(
    ! [A_18] :
      ( v1_tops_2(u1_pre_topc(A_18),A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_320,plain,
    ( v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_18])).

tff(c_338,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_320])).

tff(c_1499,plain,(
    ! [B_167,A_168] :
      ( v1_tops_2(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168))))))
      | ~ v1_tops_2(B_167,g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1517,plain,(
    ! [B_167] :
      ( v1_tops_2(B_167,'#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))))
      | ~ v1_tops_2(B_167,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1499])).

tff(c_1532,plain,(
    ! [B_167] :
      ( v1_tops_2(B_167,'#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_167,k6_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_71,c_179,c_1517])).

tff(c_1535,plain,(
    ! [B_169] :
      ( v1_tops_2(B_169,'#skF_2')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ v1_tops_2(B_169,k6_tmap_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1532])).

tff(c_1541,plain,
    ( v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),k6_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_295,c_1535])).

tff(c_1549,plain,(
    v1_tops_2(k5_tmap_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_1541])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_988,c_1549])).

tff(c_1552,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1552])).

tff(c_1561,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1560,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1581,plain,(
    ! [B_179,A_180] :
      ( r2_hidden(B_179,u1_pre_topc(A_180))
      | ~ v3_pre_topc(B_179,A_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1587,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1581])).

tff(c_1591,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1560,c_1587])).

tff(c_2052,plain,(
    ! [A_218,B_219] :
      ( k5_tmap_1(A_218,B_219) = u1_pre_topc(A_218)
      | ~ r2_hidden(B_219,u1_pre_topc(A_218))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2067,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_2052])).

tff(c_2078,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1591,c_2067])).

tff(c_2079,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2078])).

tff(c_2168,plain,(
    ! [A_222,B_223] :
      ( g1_pre_topc(u1_struct_0(A_222),k5_tmap_1(A_222,B_223)) = k6_tmap_1(A_222,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2176,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_2168])).

tff(c_2183,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2079,c_2176])).

tff(c_2185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1561,c_2183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.74  
% 4.23/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.74  %$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.23/1.74  
% 4.23/1.74  %Foreground sorts:
% 4.23/1.74  
% 4.23/1.74  
% 4.23/1.74  %Background operators:
% 4.23/1.74  
% 4.23/1.74  
% 4.23/1.74  %Foreground operators:
% 4.23/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.23/1.74  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.23/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.74  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.23/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.74  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.23/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.23/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.74  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.23/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.74  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.23/1.74  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 4.23/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.23/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.74  
% 4.23/1.78  tff(f_160, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 4.23/1.78  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 4.23/1.78  tff(f_105, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 4.23/1.78  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.23/1.78  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 4.23/1.78  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 4.23/1.78  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => v1_tops_2(u1_pre_topc(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_compts_1)).
% 4.23/1.78  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_compts_1)).
% 4.23/1.78  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.23/1.78  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 4.23/1.78  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 4.23/1.78  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.23/1.78  tff(c_60, plain, (v3_pre_topc('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.23/1.78  tff(c_71, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 4.23/1.78  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.23/1.78  tff(c_72, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 4.23/1.78  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.23/1.78  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.23/1.78  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.23/1.78  tff(c_273, plain, (![A_82, B_83]: (u1_pre_topc(k6_tmap_1(A_82, B_83))=k5_tmap_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.23/1.78  tff(c_285, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_273])).
% 4.23/1.78  tff(c_292, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_285])).
% 4.23/1.78  tff(c_293, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_292])).
% 4.23/1.78  tff(c_106, plain, (![A_54, B_55]: (l1_pre_topc(k6_tmap_1(A_54, B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.23/1.78  tff(c_112, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_106])).
% 4.23/1.78  tff(c_116, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_112])).
% 4.23/1.78  tff(c_117, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_116])).
% 4.23/1.78  tff(c_168, plain, (![A_75, B_76]: (u1_struct_0(k6_tmap_1(A_75, B_76))=u1_struct_0(A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.23/1.78  tff(c_174, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_168])).
% 4.23/1.78  tff(c_178, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_174])).
% 4.23/1.78  tff(c_179, plain, (u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_178])).
% 4.23/1.78  tff(c_8, plain, (![A_7]: (m1_subset_1(u1_pre_topc(A_7), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.23/1.78  tff(c_205, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_8])).
% 4.23/1.78  tff(c_225, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_205])).
% 4.23/1.78  tff(c_295, plain, (m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_225])).
% 4.23/1.78  tff(c_14, plain, (![A_8, B_14]: (r2_hidden('#skF_1'(A_8, B_14), B_14) | v1_tops_2(B_14, A_8) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.23/1.78  tff(c_341, plain, (r2_hidden('#skF_1'('#skF_2', k5_tmap_1('#skF_2', '#skF_3')), k5_tmap_1('#skF_2', '#skF_3')) | v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_295, c_14])).
% 4.23/1.78  tff(c_346, plain, (r2_hidden('#skF_1'('#skF_2', k5_tmap_1('#skF_2', '#skF_3')), k5_tmap_1('#skF_2', '#skF_3')) | v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_341])).
% 4.23/1.78  tff(c_566, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_346])).
% 4.23/1.78  tff(c_150, plain, (![B_70, A_71]: (r2_hidden(B_70, k5_tmap_1(A_71, B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.23/1.78  tff(c_154, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_150])).
% 4.23/1.78  tff(c_158, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_154])).
% 4.23/1.78  tff(c_159, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_158])).
% 4.23/1.78  tff(c_810, plain, (![C_117, A_118, B_119]: (v3_pre_topc(C_117, A_118) | ~r2_hidden(C_117, B_119) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~v1_tops_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_118)))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.23/1.78  tff(c_975, plain, (![A_144]: (v3_pre_topc('#skF_3', A_144) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_144))) | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), A_144) | ~m1_subset_1(k5_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_144)))) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_159, c_810])).
% 4.23/1.78  tff(c_978, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_295, c_975])).
% 4.23/1.78  tff(c_984, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_566, c_46, c_978])).
% 4.23/1.78  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_984])).
% 4.23/1.78  tff(c_988, plain, (~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_346])).
% 4.23/1.78  tff(c_18, plain, (![A_18]: (v1_tops_2(u1_pre_topc(A_18), A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.23/1.78  tff(c_320, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_18])).
% 4.23/1.78  tff(c_338, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_320])).
% 4.23/1.78  tff(c_1499, plain, (![B_167, A_168]: (v1_tops_2(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168)))))) | ~v1_tops_2(B_167, g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.23/1.78  tff(c_1517, plain, (![B_167]: (v1_tops_2(B_167, '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))))) | ~v1_tops_2(B_167, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1499])).
% 4.23/1.78  tff(c_1532, plain, (![B_167]: (v1_tops_2(B_167, '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_167, k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_71, c_179, c_1517])).
% 4.23/1.78  tff(c_1535, plain, (![B_169]: (v1_tops_2(B_169, '#skF_2') | ~m1_subset_1(B_169, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~v1_tops_2(B_169, k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1532])).
% 4.23/1.78  tff(c_1541, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2') | ~v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), k6_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_295, c_1535])).
% 4.23/1.78  tff(c_1549, plain, (v1_tops_2(k5_tmap_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_1541])).
% 4.23/1.78  tff(c_1551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_988, c_1549])).
% 4.23/1.78  tff(c_1552, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 4.23/1.78  tff(c_1559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_1552])).
% 4.23/1.78  tff(c_1561, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 4.23/1.78  tff(c_1560, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 4.23/1.78  tff(c_1581, plain, (![B_179, A_180]: (r2_hidden(B_179, u1_pre_topc(A_180)) | ~v3_pre_topc(B_179, A_180) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.23/1.78  tff(c_1587, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_1581])).
% 4.23/1.78  tff(c_1591, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1560, c_1587])).
% 4.23/1.78  tff(c_2052, plain, (![A_218, B_219]: (k5_tmap_1(A_218, B_219)=u1_pre_topc(A_218) | ~r2_hidden(B_219, u1_pre_topc(A_218)) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.23/1.78  tff(c_2067, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_2052])).
% 4.23/1.78  tff(c_2078, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1591, c_2067])).
% 4.23/1.78  tff(c_2079, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_2078])).
% 4.23/1.78  tff(c_2168, plain, (![A_222, B_223]: (g1_pre_topc(u1_struct_0(A_222), k5_tmap_1(A_222, B_223))=k6_tmap_1(A_222, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.23/1.78  tff(c_2176, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_2168])).
% 4.23/1.78  tff(c_2183, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2079, c_2176])).
% 4.23/1.78  tff(c_2185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1561, c_2183])).
% 4.23/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.78  
% 4.23/1.78  Inference rules
% 4.23/1.78  ----------------------
% 4.23/1.78  #Ref     : 0
% 4.23/1.78  #Sup     : 397
% 4.23/1.78  #Fact    : 0
% 4.23/1.78  #Define  : 0
% 4.23/1.78  #Split   : 13
% 4.23/1.78  #Chain   : 0
% 4.23/1.78  #Close   : 0
% 4.23/1.78  
% 4.23/1.78  Ordering : KBO
% 4.23/1.78  
% 4.23/1.78  Simplification rules
% 4.23/1.78  ----------------------
% 4.23/1.78  #Subsume      : 51
% 4.23/1.78  #Demod        : 628
% 4.23/1.78  #Tautology    : 154
% 4.23/1.78  #SimpNegUnit  : 92
% 4.23/1.78  #BackRed      : 17
% 4.23/1.78  
% 4.23/1.78  #Partial instantiations: 0
% 4.23/1.78  #Strategies tried      : 1
% 4.23/1.78  
% 4.23/1.78  Timing (in seconds)
% 4.23/1.78  ----------------------
% 4.23/1.78  Preprocessing        : 0.35
% 4.23/1.78  Parsing              : 0.19
% 4.23/1.78  CNF conversion       : 0.02
% 4.23/1.78  Main loop            : 0.63
% 4.23/1.78  Inferencing          : 0.22
% 4.23/1.78  Reduction            : 0.22
% 4.23/1.78  Demodulation         : 0.15
% 4.23/1.78  BG Simplification    : 0.03
% 4.23/1.78  Subsumption          : 0.12
% 4.23/1.78  Abstraction          : 0.03
% 4.23/1.78  MUC search           : 0.00
% 4.23/1.78  Cooper               : 0.00
% 4.23/1.78  Total                : 1.04
% 4.23/1.78  Index Insertion      : 0.00
% 4.23/1.78  Index Deletion       : 0.00
% 4.23/1.78  Index Matching       : 0.00
% 4.23/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
