%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:59 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  148 (1582 expanded)
%              Number of leaves         :   31 ( 545 expanded)
%              Depth                    :   24
%              Number of atoms          :  369 (4561 expanded)
%              Number of equality atoms :   12 ( 482 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(c_46,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_1'(A_52),u1_pre_topc(A_52))
      | v3_tdlat_3(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    ! [A_51] :
      ( m1_pre_topc(A_51,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_130,plain,(
    ! [A_83,B_84] :
      ( m1_pre_topc(A_83,g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)))
      | ~ m1_pre_topc(A_83,B_84)
      | ~ l1_pre_topc(B_84)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,(
    ! [A_83] :
      ( m1_pre_topc(A_83,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_83,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_130])).

tff(c_158,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_143])).

tff(c_18,plain,(
    ! [B_18,A_16] :
      ( m1_pre_topc(B_18,A_16)
      | ~ m1_pre_topc(B_18,g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_164,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_158,c_18])).

tff(c_173,plain,(
    ! [A_87] :
      ( m1_pre_topc(A_87,'#skF_3')
      | ~ m1_pre_topc(A_87,'#skF_2')
      | ~ l1_pre_topc(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_180,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_184,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_180])).

tff(c_109,plain,(
    ! [B_77,A_78] :
      ( m1_pre_topc(B_77,A_78)
      | ~ m1_pre_topc(B_77,g1_pre_topc(u1_struct_0(A_78),u1_pre_topc(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    ! [B_77] :
      ( m1_pre_topc(B_77,'#skF_2')
      | ~ m1_pre_topc(B_77,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_109])).

tff(c_118,plain,(
    ! [B_77] :
      ( m1_pre_topc(B_77,'#skF_2')
      | ~ m1_pre_topc(B_77,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_112])).

tff(c_134,plain,(
    ! [A_83] :
      ( m1_pre_topc(A_83,'#skF_2')
      | ~ m1_pre_topc(A_83,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_130,c_118])).

tff(c_146,plain,(
    ! [A_83] :
      ( m1_pre_topc(A_83,'#skF_2')
      | ~ m1_pre_topc(A_83,'#skF_3')
      | ~ l1_pre_topc(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_134])).

tff(c_100,plain,(
    ! [B_73,A_74] :
      ( m1_subset_1(u1_struct_0(B_73),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(u1_struct_0(B_73),u1_struct_0(A_74))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_105,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0(A_76))
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [B_88,A_89] :
      ( u1_struct_0(B_88) = u1_struct_0(A_89)
      | ~ r1_tarski(u1_struct_0(A_89),u1_struct_0(B_88))
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_202,plain,(
    ! [B_90,A_91] :
      ( u1_struct_0(B_90) = u1_struct_0(A_91)
      | ~ m1_pre_topc(A_91,B_90)
      | ~ l1_pre_topc(B_90)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_104,c_191])).

tff(c_204,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_202])).

tff(c_215,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_204])).

tff(c_223,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_226,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_146,c_223])).

tff(c_229,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_226])).

tff(c_243,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_229])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_243])).

tff(c_248,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_34,plain,(
    ! [B_50,A_48] :
      ( m1_subset_1(u1_struct_0(B_50),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_pre_topc(B_50,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_346,plain,(
    ! [B_50] :
      ( m1_subset_1(u1_struct_0(B_50),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_50,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_34])).

tff(c_431,plain,(
    ! [B_98] :
      ( m1_subset_1(u1_struct_0(B_98),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_98,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_346])).

tff(c_437,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_431])).

tff(c_3486,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_3489,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_3486])).

tff(c_3496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_184,c_3489])).

tff(c_3498,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_44,plain,(
    ! [A_52] :
      ( m1_subset_1('#skF_1'(A_52),k1_zfmisc_1(u1_struct_0(A_52)))
      | v3_tdlat_3(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3470,plain,(
    ! [C_257,A_258,B_259] :
      ( m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(B_259)))
      | ~ m1_pre_topc(B_259,A_258)
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7176,plain,(
    ! [C_449,A_450] :
      ( m1_subset_1(C_449,k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ m1_subset_1(C_449,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_2',A_450)
      | ~ l1_pre_topc(A_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_3470])).

tff(c_7189,plain,(
    ! [A_450] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ m1_pre_topc('#skF_2',A_450)
      | ~ l1_pre_topc(A_450)
      | v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_7176])).

tff(c_7203,plain,(
    ! [A_450] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ m1_pre_topc('#skF_2',A_450)
      | ~ l1_pre_topc(A_450)
      | v3_tdlat_3('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7189])).

tff(c_7206,plain,(
    ! [A_451] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ m1_pre_topc('#skF_2',A_451)
      | ~ l1_pre_topc(A_451) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_7203])).

tff(c_7217,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_7206])).

tff(c_7224,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3498,c_7217])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_14,plain,(
    ! [A_8] :
      ( m1_subset_1(u1_pre_topc(A_8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_358,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_14])).

tff(c_385,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_358])).

tff(c_249,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_596,plain,(
    ! [B_106,A_107] :
      ( v1_tops_2(B_106,A_107)
      | ~ r1_tarski(B_106,u1_pre_topc(A_107))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_602,plain,(
    ! [B_106] :
      ( v1_tops_2(B_106,'#skF_2')
      | ~ r1_tarski(B_106,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_596])).

tff(c_685,plain,(
    ! [B_111] :
      ( v1_tops_2(B_111,'#skF_2')
      | ~ r1_tarski(B_111,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_602])).

tff(c_688,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_385,c_685])).

tff(c_699,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_688])).

tff(c_397,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(B_95,u1_pre_topc(A_96))
      | ~ v1_tops_2(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_400,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_385,c_397])).

tff(c_413,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_400])).

tff(c_439,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_986,plain,(
    ! [D_129,C_130,A_131] :
      ( v1_tops_2(D_129,C_130)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_130))))
      | ~ v1_tops_2(D_129,A_131)
      | ~ m1_pre_topc(C_130,A_131)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_994,plain,(
    ! [A_131] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_131)
      | ~ m1_pre_topc('#skF_3',A_131)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_385,c_986])).

tff(c_3420,plain,(
    ! [A_256] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_256)
      | ~ m1_pre_topc('#skF_3',A_256)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_256))))
      | ~ l1_pre_topc(A_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_994])).

tff(c_3441,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_3420])).

tff(c_3464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_385,c_249,c_699,c_3441])).

tff(c_3465,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_3469,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3465,c_2])).

tff(c_3528,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3469])).

tff(c_403,plain,(
    ! [B_95] :
      ( r1_tarski(B_95,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_95,'#skF_2')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_397])).

tff(c_3758,plain,(
    ! [B_274] :
      ( r1_tarski(B_274,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_274,'#skF_2')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_403])).

tff(c_3769,plain,
    ( r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3758])).

tff(c_3781,plain,
    ( r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3769])).

tff(c_3782,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3528,c_3781])).

tff(c_171,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,'#skF_3')
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_254,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_249,c_171])).

tff(c_263,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_254])).

tff(c_3650,plain,(
    ! [C_266,A_267,B_268] :
      ( m1_subset_1(C_266,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_267))))
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_268))))
      | ~ m1_pre_topc(B_268,A_267)
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3879,plain,(
    ! [A_280,A_281] :
      ( m1_subset_1(u1_pre_topc(A_280),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_281))))
      | ~ m1_pre_topc(A_280,A_281)
      | ~ l1_pre_topc(A_281)
      | ~ l1_pre_topc(A_280) ) ),
    inference(resolution,[status(thm)],[c_14,c_3650])).

tff(c_24,plain,(
    ! [C_28,A_22,B_26] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_26))))
      | ~ m1_pre_topc(B_26,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5460,plain,(
    ! [A_376,A_377,A_378] :
      ( m1_subset_1(u1_pre_topc(A_376),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_377))))
      | ~ m1_pre_topc(A_378,A_377)
      | ~ l1_pre_topc(A_377)
      | ~ m1_pre_topc(A_376,A_378)
      | ~ l1_pre_topc(A_378)
      | ~ l1_pre_topc(A_376) ) ),
    inference(resolution,[status(thm)],[c_3879,c_24])).

tff(c_5474,plain,(
    ! [A_376,A_83] :
      ( m1_subset_1(u1_pre_topc(A_376),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_376,A_83)
      | ~ l1_pre_topc(A_376)
      | ~ m1_pre_topc(A_83,'#skF_3')
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_146,c_5460])).

tff(c_6130,plain,(
    ! [A_406,A_407] :
      ( m1_subset_1(u1_pre_topc(A_406),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_406,A_407)
      | ~ l1_pre_topc(A_406)
      | ~ m1_pre_topc(A_407,'#skF_3')
      | ~ l1_pre_topc(A_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_248,c_5474])).

tff(c_6138,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_6130])).

tff(c_6158,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_184,c_52,c_6138])).

tff(c_6200,plain,(
    r1_tarski(u1_pre_topc('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6158,c_8])).

tff(c_3901,plain,(
    ! [A_280] :
      ( m1_subset_1(u1_pre_topc(A_280),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_280,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_3879])).

tff(c_3914,plain,(
    ! [A_282] :
      ( m1_subset_1(u1_pre_topc(A_282),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_282,'#skF_2')
      | ~ l1_pre_topc(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3901])).

tff(c_28,plain,(
    ! [B_46,A_44] :
      ( v1_tops_2(B_46,A_44)
      | ~ r1_tarski(B_46,u1_pre_topc(A_44))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44))))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3925,plain,(
    ! [A_282] :
      ( v1_tops_2(u1_pre_topc(A_282),'#skF_3')
      | ~ r1_tarski(u1_pre_topc(A_282),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_282,'#skF_2')
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_3914,c_28])).

tff(c_5167,plain,(
    ! [A_359] :
      ( v1_tops_2(u1_pre_topc(A_359),'#skF_3')
      | ~ r1_tarski(u1_pre_topc(A_359),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(A_359,'#skF_2')
      | ~ l1_pre_topc(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3925])).

tff(c_5174,plain,
    ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_5167])).

tff(c_5180,plain,(
    v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_249,c_5174])).

tff(c_6193,plain,(
    ! [A_22] :
      ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ m1_pre_topc('#skF_3',A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_6158,c_24])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3954,plain,(
    ! [D_284,C_285,A_286] :
      ( v1_tops_2(D_284,C_285)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_285))))
      | ~ v1_tops_2(D_284,A_286)
      | ~ m1_pre_topc(C_285,A_286)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_286))))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5189,plain,(
    ! [A_361,C_362,A_363] :
      ( v1_tops_2(A_361,C_362)
      | ~ v1_tops_2(A_361,A_363)
      | ~ m1_pre_topc(C_362,A_363)
      | ~ m1_subset_1(A_361,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_363))))
      | ~ l1_pre_topc(A_363)
      | ~ r1_tarski(A_361,k1_zfmisc_1(u1_struct_0(C_362))) ) ),
    inference(resolution,[status(thm)],[c_10,c_3954])).

tff(c_5199,plain,(
    ! [A_361] :
      ( v1_tops_2(A_361,'#skF_2')
      | ~ v1_tops_2(A_361,'#skF_3')
      | ~ m1_subset_1(A_361,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_361,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_184,c_5189])).

tff(c_6780,plain,(
    ! [A_431] :
      ( v1_tops_2(A_431,'#skF_2')
      | ~ v1_tops_2(A_431,'#skF_3')
      | ~ m1_subset_1(A_431,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ r1_tarski(A_431,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_52,c_5199])).

tff(c_6784,plain,
    ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ r1_tarski(u1_pre_topc('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6193,c_6780])).

tff(c_6825,plain,(
    v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_263,c_6200,c_5180,c_6784])).

tff(c_6827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3782,c_6825])).

tff(c_6828,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3469])).

tff(c_7103,plain,(
    ! [A_444,B_445] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_444),B_445),u1_pre_topc(A_444))
      | ~ r2_hidden(B_445,u1_pre_topc(A_444))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ v3_tdlat_3(A_444)
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7113,plain,(
    ! [B_445] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_445),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_445,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_7103])).

tff(c_9848,plain,(
    ! [B_586] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_586),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_586,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_586,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_248,c_6828,c_6828,c_7113])).

tff(c_40,plain,(
    ! [A_52] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_52),'#skF_1'(A_52)),u1_pre_topc(A_52))
      | v3_tdlat_3(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_9852,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_9848,c_40])).

tff(c_9855,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7224,c_52,c_9852])).

tff(c_9856,plain,(
    ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_9855])).

tff(c_9859,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_9856])).

tff(c_9862,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9859])).

tff(c_9864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_9862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.70  
% 7.83/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.70  %$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 7.83/2.70  
% 7.83/2.70  %Foreground sorts:
% 7.83/2.70  
% 7.83/2.70  
% 7.83/2.70  %Background operators:
% 7.83/2.70  
% 7.83/2.70  
% 7.83/2.70  %Foreground operators:
% 7.83/2.70  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.83/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.83/2.70  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.83/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.83/2.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.83/2.70  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 7.83/2.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.83/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.83/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.83/2.70  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.83/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.83/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.83/2.70  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 7.83/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.83/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.83/2.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.83/2.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.83/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.83/2.70  
% 7.83/2.73  tff(f_146, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 7.83/2.73  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 7.83/2.73  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.83/2.73  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 7.83/2.73  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 7.83/2.73  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.83/2.73  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.83/2.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.83/2.73  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 7.83/2.73  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.83/2.73  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 7.83/2.73  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 7.83/2.73  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 7.83/2.73  tff(c_46, plain, (~v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.83/2.73  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.83/2.73  tff(c_42, plain, (![A_52]: (r2_hidden('#skF_1'(A_52), u1_pre_topc(A_52)) | v3_tdlat_3(A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.83/2.73  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.83/2.73  tff(c_36, plain, (![A_51]: (m1_pre_topc(A_51, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.83/2.73  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.83/2.73  tff(c_130, plain, (![A_83, B_84]: (m1_pre_topc(A_83, g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))) | ~m1_pre_topc(A_83, B_84) | ~l1_pre_topc(B_84) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.83/2.73  tff(c_143, plain, (![A_83]: (m1_pre_topc(A_83, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_83, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_83))), inference(superposition, [status(thm), theory('equality')], [c_50, c_130])).
% 7.83/2.73  tff(c_158, plain, (![A_86]: (m1_pre_topc(A_86, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_143])).
% 7.83/2.73  tff(c_18, plain, (![B_18, A_16]: (m1_pre_topc(B_18, A_16) | ~m1_pre_topc(B_18, g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/2.73  tff(c_164, plain, (![A_86]: (m1_pre_topc(A_86, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_158, c_18])).
% 7.83/2.73  tff(c_173, plain, (![A_87]: (m1_pre_topc(A_87, '#skF_3') | ~m1_pre_topc(A_87, '#skF_2') | ~l1_pre_topc(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_164])).
% 7.83/2.73  tff(c_180, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_173])).
% 7.83/2.73  tff(c_184, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_180])).
% 7.83/2.73  tff(c_109, plain, (![B_77, A_78]: (m1_pre_topc(B_77, A_78) | ~m1_pre_topc(B_77, g1_pre_topc(u1_struct_0(A_78), u1_pre_topc(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.83/2.73  tff(c_112, plain, (![B_77]: (m1_pre_topc(B_77, '#skF_2') | ~m1_pre_topc(B_77, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_109])).
% 7.83/2.73  tff(c_118, plain, (![B_77]: (m1_pre_topc(B_77, '#skF_2') | ~m1_pre_topc(B_77, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_112])).
% 7.83/2.73  tff(c_134, plain, (![A_83]: (m1_pre_topc(A_83, '#skF_2') | ~m1_pre_topc(A_83, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_130, c_118])).
% 7.83/2.73  tff(c_146, plain, (![A_83]: (m1_pre_topc(A_83, '#skF_2') | ~m1_pre_topc(A_83, '#skF_3') | ~l1_pre_topc(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_134])).
% 7.83/2.73  tff(c_100, plain, (![B_73, A_74]: (m1_subset_1(u1_struct_0(B_73), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.73  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.83/2.73  tff(c_104, plain, (![B_73, A_74]: (r1_tarski(u1_struct_0(B_73), u1_struct_0(A_74)) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_100, c_8])).
% 7.83/2.73  tff(c_105, plain, (![B_75, A_76]: (r1_tarski(u1_struct_0(B_75), u1_struct_0(A_76)) | ~m1_pre_topc(B_75, A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_100, c_8])).
% 7.83/2.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.83/2.73  tff(c_191, plain, (![B_88, A_89]: (u1_struct_0(B_88)=u1_struct_0(A_89) | ~r1_tarski(u1_struct_0(A_89), u1_struct_0(B_88)) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_105, c_2])).
% 7.83/2.73  tff(c_202, plain, (![B_90, A_91]: (u1_struct_0(B_90)=u1_struct_0(A_91) | ~m1_pre_topc(A_91, B_90) | ~l1_pre_topc(B_90) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_104, c_191])).
% 7.83/2.73  tff(c_204, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_184, c_202])).
% 7.83/2.73  tff(c_215, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_204])).
% 7.83/2.73  tff(c_223, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_215])).
% 7.83/2.73  tff(c_226, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_146, c_223])).
% 7.83/2.73  tff(c_229, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_226])).
% 7.83/2.73  tff(c_243, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_229])).
% 7.83/2.73  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_243])).
% 7.83/2.73  tff(c_248, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_215])).
% 7.83/2.73  tff(c_34, plain, (![B_50, A_48]: (m1_subset_1(u1_struct_0(B_50), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_pre_topc(B_50, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.83/2.73  tff(c_346, plain, (![B_50]: (m1_subset_1(u1_struct_0(B_50), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_50, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_34])).
% 7.83/2.73  tff(c_431, plain, (![B_98]: (m1_subset_1(u1_struct_0(B_98), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_98, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_346])).
% 7.83/2.73  tff(c_437, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_431])).
% 7.83/2.73  tff(c_3486, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_437])).
% 7.83/2.73  tff(c_3489, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_146, c_3486])).
% 7.83/2.73  tff(c_3496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_184, c_3489])).
% 7.83/2.73  tff(c_3498, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_437])).
% 7.83/2.73  tff(c_44, plain, (![A_52]: (m1_subset_1('#skF_1'(A_52), k1_zfmisc_1(u1_struct_0(A_52))) | v3_tdlat_3(A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.83/2.73  tff(c_3470, plain, (![C_257, A_258, B_259]: (m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_258))) | ~m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(B_259))) | ~m1_pre_topc(B_259, A_258) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.83/2.73  tff(c_7176, plain, (![C_449, A_450]: (m1_subset_1(C_449, k1_zfmisc_1(u1_struct_0(A_450))) | ~m1_subset_1(C_449, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', A_450) | ~l1_pre_topc(A_450))), inference(superposition, [status(thm), theory('equality')], [c_248, c_3470])).
% 7.83/2.73  tff(c_7189, plain, (![A_450]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_450))) | ~m1_pre_topc('#skF_2', A_450) | ~l1_pre_topc(A_450) | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_7176])).
% 7.83/2.73  tff(c_7203, plain, (![A_450]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_450))) | ~m1_pre_topc('#skF_2', A_450) | ~l1_pre_topc(A_450) | v3_tdlat_3('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7189])).
% 7.83/2.73  tff(c_7206, plain, (![A_451]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_451))) | ~m1_pre_topc('#skF_2', A_451) | ~l1_pre_topc(A_451))), inference(negUnitSimplification, [status(thm)], [c_46, c_7203])).
% 7.83/2.73  tff(c_7217, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_7206])).
% 7.83/2.73  tff(c_7224, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3498, c_7217])).
% 7.83/2.73  tff(c_48, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.83/2.73  tff(c_14, plain, (![A_8]: (m1_subset_1(u1_pre_topc(A_8), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.83/2.73  tff(c_358, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_14])).
% 7.83/2.73  tff(c_385, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_358])).
% 7.83/2.73  tff(c_249, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_215])).
% 7.83/2.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.83/2.73  tff(c_596, plain, (![B_106, A_107]: (v1_tops_2(B_106, A_107) | ~r1_tarski(B_106, u1_pre_topc(A_107)) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.83/2.73  tff(c_602, plain, (![B_106]: (v1_tops_2(B_106, '#skF_2') | ~r1_tarski(B_106, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_596])).
% 7.83/2.73  tff(c_685, plain, (![B_111]: (v1_tops_2(B_111, '#skF_2') | ~r1_tarski(B_111, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_111, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_602])).
% 7.83/2.73  tff(c_688, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_385, c_685])).
% 7.83/2.73  tff(c_699, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_688])).
% 7.83/2.73  tff(c_397, plain, (![B_95, A_96]: (r1_tarski(B_95, u1_pre_topc(A_96)) | ~v1_tops_2(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.83/2.73  tff(c_400, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_385, c_397])).
% 7.83/2.73  tff(c_413, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_400])).
% 7.83/2.73  tff(c_439, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_413])).
% 7.83/2.73  tff(c_986, plain, (![D_129, C_130, A_131]: (v1_tops_2(D_129, C_130) | ~m1_subset_1(D_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_130)))) | ~v1_tops_2(D_129, A_131) | ~m1_pre_topc(C_130, A_131) | ~m1_subset_1(D_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.83/2.73  tff(c_994, plain, (![A_131]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_131) | ~m1_pre_topc('#skF_3', A_131) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_385, c_986])).
% 7.83/2.73  tff(c_3420, plain, (![A_256]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_256) | ~m1_pre_topc('#skF_3', A_256) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_256)))) | ~l1_pre_topc(A_256))), inference(negUnitSimplification, [status(thm)], [c_439, c_994])).
% 7.83/2.73  tff(c_3441, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_3420])).
% 7.83/2.73  tff(c_3464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_385, c_249, c_699, c_3441])).
% 7.83/2.73  tff(c_3465, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_413])).
% 7.83/2.73  tff(c_3469, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_3465, c_2])).
% 7.83/2.73  tff(c_3528, plain, (~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_3469])).
% 7.83/2.73  tff(c_403, plain, (![B_95]: (r1_tarski(B_95, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_95, '#skF_2') | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_397])).
% 7.83/2.73  tff(c_3758, plain, (![B_274]: (r1_tarski(B_274, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_274, '#skF_2') | ~m1_subset_1(B_274, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_403])).
% 7.83/2.73  tff(c_3769, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3758])).
% 7.83/2.73  tff(c_3781, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3769])).
% 7.83/2.73  tff(c_3782, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3528, c_3781])).
% 7.83/2.73  tff(c_171, plain, (![A_86]: (m1_pre_topc(A_86, '#skF_3') | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_164])).
% 7.83/2.73  tff(c_254, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_249, c_171])).
% 7.83/2.73  tff(c_263, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_254])).
% 7.83/2.73  tff(c_3650, plain, (![C_266, A_267, B_268]: (m1_subset_1(C_266, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_267)))) | ~m1_subset_1(C_266, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_268)))) | ~m1_pre_topc(B_268, A_267) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.83/2.73  tff(c_3879, plain, (![A_280, A_281]: (m1_subset_1(u1_pre_topc(A_280), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_281)))) | ~m1_pre_topc(A_280, A_281) | ~l1_pre_topc(A_281) | ~l1_pre_topc(A_280))), inference(resolution, [status(thm)], [c_14, c_3650])).
% 7.83/2.73  tff(c_24, plain, (![C_28, A_22, B_26]: (m1_subset_1(C_28, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_26)))) | ~m1_pre_topc(B_26, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.83/2.73  tff(c_5460, plain, (![A_376, A_377, A_378]: (m1_subset_1(u1_pre_topc(A_376), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_377)))) | ~m1_pre_topc(A_378, A_377) | ~l1_pre_topc(A_377) | ~m1_pre_topc(A_376, A_378) | ~l1_pre_topc(A_378) | ~l1_pre_topc(A_376))), inference(resolution, [status(thm)], [c_3879, c_24])).
% 7.83/2.73  tff(c_5474, plain, (![A_376, A_83]: (m1_subset_1(u1_pre_topc(A_376), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_376, A_83) | ~l1_pre_topc(A_376) | ~m1_pre_topc(A_83, '#skF_3') | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_146, c_5460])).
% 7.83/2.73  tff(c_6130, plain, (![A_406, A_407]: (m1_subset_1(u1_pre_topc(A_406), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_406, A_407) | ~l1_pre_topc(A_406) | ~m1_pre_topc(A_407, '#skF_3') | ~l1_pre_topc(A_407))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_248, c_5474])).
% 7.83/2.73  tff(c_6138, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_249, c_6130])).
% 7.83/2.73  tff(c_6158, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_184, c_52, c_6138])).
% 7.83/2.73  tff(c_6200, plain, (r1_tarski(u1_pre_topc('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6158, c_8])).
% 7.83/2.73  tff(c_3901, plain, (![A_280]: (m1_subset_1(u1_pre_topc(A_280), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_280, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_280))), inference(superposition, [status(thm), theory('equality')], [c_248, c_3879])).
% 7.83/2.73  tff(c_3914, plain, (![A_282]: (m1_subset_1(u1_pre_topc(A_282), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_282, '#skF_2') | ~l1_pre_topc(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3901])).
% 7.83/2.73  tff(c_28, plain, (![B_46, A_44]: (v1_tops_2(B_46, A_44) | ~r1_tarski(B_46, u1_pre_topc(A_44)) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_44)))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.83/2.73  tff(c_3925, plain, (![A_282]: (v1_tops_2(u1_pre_topc(A_282), '#skF_3') | ~r1_tarski(u1_pre_topc(A_282), u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_282, '#skF_2') | ~l1_pre_topc(A_282))), inference(resolution, [status(thm)], [c_3914, c_28])).
% 7.83/2.73  tff(c_5167, plain, (![A_359]: (v1_tops_2(u1_pre_topc(A_359), '#skF_3') | ~r1_tarski(u1_pre_topc(A_359), u1_pre_topc('#skF_3')) | ~m1_pre_topc(A_359, '#skF_2') | ~l1_pre_topc(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3925])).
% 7.83/2.73  tff(c_5174, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_5167])).
% 7.83/2.73  tff(c_5180, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_249, c_5174])).
% 7.83/2.73  tff(c_6193, plain, (![A_22]: (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~m1_pre_topc('#skF_3', A_22) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_6158, c_24])).
% 7.83/2.73  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.83/2.73  tff(c_3954, plain, (![D_284, C_285, A_286]: (v1_tops_2(D_284, C_285) | ~m1_subset_1(D_284, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_285)))) | ~v1_tops_2(D_284, A_286) | ~m1_pre_topc(C_285, A_286) | ~m1_subset_1(D_284, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_286)))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.83/2.73  tff(c_5189, plain, (![A_361, C_362, A_363]: (v1_tops_2(A_361, C_362) | ~v1_tops_2(A_361, A_363) | ~m1_pre_topc(C_362, A_363) | ~m1_subset_1(A_361, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_363)))) | ~l1_pre_topc(A_363) | ~r1_tarski(A_361, k1_zfmisc_1(u1_struct_0(C_362))))), inference(resolution, [status(thm)], [c_10, c_3954])).
% 7.83/2.73  tff(c_5199, plain, (![A_361]: (v1_tops_2(A_361, '#skF_2') | ~v1_tops_2(A_361, '#skF_3') | ~m1_subset_1(A_361, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_361, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_184, c_5189])).
% 7.83/2.73  tff(c_6780, plain, (![A_431]: (v1_tops_2(A_431, '#skF_2') | ~v1_tops_2(A_431, '#skF_3') | ~m1_subset_1(A_431, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~r1_tarski(A_431, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_52, c_5199])).
% 7.83/2.73  tff(c_6784, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6193, c_6780])).
% 7.83/2.73  tff(c_6825, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_263, c_6200, c_5180, c_6784])).
% 7.83/2.73  tff(c_6827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3782, c_6825])).
% 7.83/2.73  tff(c_6828, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_3469])).
% 7.83/2.73  tff(c_7103, plain, (![A_444, B_445]: (r2_hidden(k6_subset_1(u1_struct_0(A_444), B_445), u1_pre_topc(A_444)) | ~r2_hidden(B_445, u1_pre_topc(A_444)) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~v3_tdlat_3(A_444) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.83/2.73  tff(c_7113, plain, (![B_445]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_445), u1_pre_topc('#skF_2')) | ~r2_hidden(B_445, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_7103])).
% 7.83/2.73  tff(c_9848, plain, (![B_586]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_586), u1_pre_topc('#skF_3')) | ~r2_hidden(B_586, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_586, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_248, c_6828, c_6828, c_7113])).
% 7.83/2.73  tff(c_40, plain, (![A_52]: (~r2_hidden(k6_subset_1(u1_struct_0(A_52), '#skF_1'(A_52)), u1_pre_topc(A_52)) | v3_tdlat_3(A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.83/2.73  tff(c_9852, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_9848, c_40])).
% 7.83/2.73  tff(c_9855, plain, (v3_tdlat_3('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7224, c_52, c_9852])).
% 7.83/2.73  tff(c_9856, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_9855])).
% 7.83/2.73  tff(c_9859, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_9856])).
% 7.83/2.73  tff(c_9862, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_9859])).
% 7.83/2.73  tff(c_9864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_9862])).
% 7.83/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.73  
% 7.83/2.73  Inference rules
% 7.83/2.73  ----------------------
% 7.83/2.73  #Ref     : 0
% 7.83/2.73  #Sup     : 1950
% 7.83/2.73  #Fact    : 0
% 7.83/2.73  #Define  : 0
% 7.83/2.73  #Split   : 15
% 7.83/2.73  #Chain   : 0
% 7.83/2.73  #Close   : 0
% 7.83/2.73  
% 7.83/2.73  Ordering : KBO
% 7.83/2.73  
% 7.83/2.73  Simplification rules
% 7.83/2.73  ----------------------
% 7.83/2.73  #Subsume      : 749
% 7.83/2.73  #Demod        : 2558
% 7.83/2.73  #Tautology    : 505
% 7.83/2.73  #SimpNegUnit  : 115
% 7.83/2.73  #BackRed      : 6
% 7.83/2.73  
% 7.83/2.73  #Partial instantiations: 0
% 7.83/2.73  #Strategies tried      : 1
% 7.83/2.73  
% 7.83/2.73  Timing (in seconds)
% 7.83/2.73  ----------------------
% 7.83/2.73  Preprocessing        : 0.32
% 7.83/2.73  Parsing              : 0.18
% 7.83/2.73  CNF conversion       : 0.02
% 7.83/2.73  Main loop            : 1.61
% 7.83/2.73  Inferencing          : 0.54
% 7.83/2.73  Reduction            : 0.52
% 7.83/2.73  Demodulation         : 0.34
% 7.83/2.73  BG Simplification    : 0.04
% 7.83/2.73  Subsumption          : 0.42
% 7.83/2.73  Abstraction          : 0.07
% 7.83/2.73  MUC search           : 0.00
% 7.83/2.73  Cooper               : 0.00
% 7.83/2.73  Total                : 1.99
% 7.83/2.73  Index Insertion      : 0.00
% 7.83/2.73  Index Deletion       : 0.00
% 7.83/2.73  Index Matching       : 0.00
% 7.83/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
