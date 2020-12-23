%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:59 EST 2020

% Result     : Theorem 9.74s
% Output     : CNFRefutation 9.74s
% Verified   : 
% Statistics : Number of formulae       :  225 (4333 expanded)
%              Number of leaves         :   31 (1431 expanded)
%              Depth                    :   33
%              Number of atoms          :  539 (12377 expanded)
%              Number of equality atoms :    7 (1017 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_111,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    ! [A_46] :
      ( m1_pre_topc(A_46,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_154,plain,(
    ! [A_85,B_86] :
      ( m1_pre_topc(A_85,g1_pre_topc(u1_struct_0(B_86),u1_pre_topc(B_86)))
      | ~ m1_pre_topc(A_85,B_86)
      | ~ l1_pre_topc(B_86)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_119,plain,(
    ! [B_75,A_76] :
      ( m1_pre_topc(B_75,A_76)
      | ~ m1_pre_topc(B_75,g1_pre_topc(u1_struct_0(A_76),u1_pre_topc(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_122,plain,(
    ! [B_75] :
      ( m1_pre_topc(B_75,'#skF_2')
      | ~ m1_pre_topc(B_75,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_119])).

tff(c_128,plain,(
    ! [B_75] :
      ( m1_pre_topc(B_75,'#skF_2')
      | ~ m1_pre_topc(B_75,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_122])).

tff(c_158,plain,(
    ! [A_85] :
      ( m1_pre_topc(A_85,'#skF_2')
      | ~ m1_pre_topc(A_85,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_154,c_128])).

tff(c_170,plain,(
    ! [A_85] :
      ( m1_pre_topc(A_85,'#skF_2')
      | ~ m1_pre_topc(A_85,'#skF_3')
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_158])).

tff(c_111,plain,(
    ! [B_73,A_74] :
      ( m1_subset_1(u1_struct_0(B_73),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(u1_struct_0(B_73),u1_struct_0(A_74))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_111,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_85] :
      ( m1_pre_topc(A_85,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_85,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_154])).

tff(c_182,plain,(
    ! [A_88] :
      ( m1_pre_topc(A_88,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_88,'#skF_2')
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_167])).

tff(c_24,plain,(
    ! [B_24,A_22] :
      ( m1_pre_topc(B_24,A_22)
      | ~ m1_pre_topc(B_24,g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_188,plain,(
    ! [A_88] :
      ( m1_pre_topc(A_88,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_88,'#skF_2')
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_182,c_24])).

tff(c_197,plain,(
    ! [A_89] :
      ( m1_pre_topc(A_89,'#skF_3')
      | ~ m1_pre_topc(A_89,'#skF_2')
      | ~ l1_pre_topc(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_188])).

tff(c_204,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_197])).

tff(c_208,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_204])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_296,plain,(
    ! [C_111,A_112,B_113] :
      ( m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(B_113)))
      | ~ m1_pre_topc(B_113,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_346,plain,(
    ! [A_119,A_120,B_121] :
      ( m1_subset_1(A_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_pre_topc(B_121,A_120)
      | ~ l1_pre_topc(A_120)
      | ~ r1_tarski(A_119,u1_struct_0(B_121)) ) ),
    inference(resolution,[status(thm)],[c_10,c_296])).

tff(c_348,plain,(
    ! [A_119] :
      ( m1_subset_1(A_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_119,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_208,c_346])).

tff(c_366,plain,(
    ! [A_122] :
      ( m1_subset_1(A_122,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_122,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_348])).

tff(c_383,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_123,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_366,c_8])).

tff(c_402,plain,(
    r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_383])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_405,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_427,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_430,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_427])).

tff(c_433,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_430])).

tff(c_436,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_433])).

tff(c_439,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_436])).

tff(c_442,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_439])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_442])).

tff(c_447,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_78,plain,(
    ! [A_62] :
      ( m1_subset_1(u1_pre_topc(A_62),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_82,plain,(
    ! [A_62] :
      ( r1_tarski(u1_pre_topc(A_62),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_78,c_8])).

tff(c_511,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_82])).

tff(c_544,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_511])).

tff(c_44,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_95,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_1'(A_68),k1_zfmisc_1(u1_struct_0(A_68)))
      | v3_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_102,plain,(
    ! [A_68] :
      ( r1_tarski('#skF_1'(A_68),u1_struct_0(A_68))
      | v3_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_95,c_8])).

tff(c_42,plain,(
    ! [A_47] :
      ( m1_subset_1('#skF_1'(A_47),k1_zfmisc_1(u1_struct_0(A_47)))
      | v3_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [B_10,A_8] :
      ( r2_hidden(B_10,u1_pre_topc(A_8))
      | ~ v3_pre_topc(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_478,plain,(
    ! [B_10] :
      ( r2_hidden(B_10,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_10,'#skF_2')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_16])).

tff(c_918,plain,(
    ! [B_147] :
      ( r2_hidden(B_147,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_147,'#skF_2')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_478])).

tff(c_947,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_918])).

tff(c_969,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_947])).

tff(c_970,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_969])).

tff(c_1001,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_970])).

tff(c_40,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_1'(A_47),u1_pre_topc(A_47))
      | v3_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_20,plain,(
    ! [A_14] :
      ( m1_subset_1(u1_pre_topc(A_14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_65,A_14] :
      ( m1_subset_1(A_65,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ r2_hidden(A_65,u1_pre_topc(A_14))
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_88])).

tff(c_228,plain,(
    ! [B_95,A_96] :
      ( v3_pre_topc(B_95,A_96)
      | ~ r2_hidden(B_95,u1_pre_topc(A_96))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_246,plain,(
    ! [A_97,A_98] :
      ( v3_pre_topc(A_97,A_98)
      | ~ r2_hidden(A_97,u1_pre_topc(A_98))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_93,c_228])).

tff(c_250,plain,(
    ! [A_47] :
      ( v3_pre_topc('#skF_1'(A_47),A_47)
      | v3_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_40,c_246])).

tff(c_371,plain,(
    ! [A_122] :
      ( r2_hidden(A_122,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_122,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_122,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_366,c_16])).

tff(c_380,plain,(
    ! [A_122] :
      ( r2_hidden(A_122,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_122,'#skF_3')
      | ~ r1_tarski(A_122,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_371])).

tff(c_760,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_136,'#skF_3')
      | ~ r1_tarski(A_136,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_380])).

tff(c_94,plain,(
    ! [A_65,B_4,A_3] :
      ( m1_subset_1(A_65,B_4)
      | ~ r2_hidden(A_65,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_1621,plain,(
    ! [A_185,B_186] :
      ( m1_subset_1(A_185,B_186)
      | ~ r1_tarski(u1_pre_topc('#skF_3'),B_186)
      | ~ v3_pre_topc(A_185,'#skF_3')
      | ~ r1_tarski(A_185,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_760,c_94])).

tff(c_1632,plain,(
    ! [A_187] :
      ( m1_subset_1(A_187,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_187,'#skF_3')
      | ~ r1_tarski(A_187,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1621])).

tff(c_1663,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_1632])).

tff(c_1684,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1663])).

tff(c_1685,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1684])).

tff(c_1687,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1685])).

tff(c_1718,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_1687])).

tff(c_1721,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1718])).

tff(c_1723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1721])).

tff(c_1725,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1685])).

tff(c_410,plain,(
    ! [D_125,C_126,A_127] :
      ( v3_pre_topc(D_125,C_126)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(C_126)))
      | ~ v3_pre_topc(D_125,A_127)
      | ~ m1_pre_topc(C_126,A_127)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_972,plain,(
    ! [A_148,C_149,A_150] :
      ( v3_pre_topc(A_148,C_149)
      | ~ v3_pre_topc(A_148,A_150)
      | ~ m1_pre_topc(C_149,A_150)
      | ~ m1_subset_1(A_148,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ r1_tarski(A_148,u1_struct_0(C_149)) ) ),
    inference(resolution,[status(thm)],[c_10,c_410])).

tff(c_978,plain,(
    ! [A_148] :
      ( v3_pre_topc(A_148,'#skF_2')
      | ~ v3_pre_topc(A_148,'#skF_3')
      | ~ m1_subset_1(A_148,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_148,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_208,c_972])).

tff(c_2720,plain,(
    ! [A_248] :
      ( v3_pre_topc(A_248,'#skF_2')
      | ~ v3_pre_topc(A_248,'#skF_3')
      | ~ m1_subset_1(A_248,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_248,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_50,c_978])).

tff(c_2772,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_2720])).

tff(c_2809,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1725,c_2772])).

tff(c_2810,plain,(
    ~ r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1001,c_2809])).

tff(c_2823,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_2810])).

tff(c_2838,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2823])).

tff(c_2840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2838])).

tff(c_2841,plain,(
    r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_2904,plain,(
    ! [B_252] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_252)
      | ~ r1_tarski(u1_pre_topc('#skF_2'),B_252) ) ),
    inference(resolution,[status(thm)],[c_2841,c_94])).

tff(c_2916,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_544,c_2904])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    ! [A_47,B_50] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_47),B_50),u1_pre_topc(A_47))
      | ~ r2_hidden(B_50,u1_pre_topc(A_47))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ v3_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_462,plain,(
    ! [B_50] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_50),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_50,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_36])).

tff(c_7095,plain,(
    ! [B_457] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_457),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_457,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_457,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_447,c_462])).

tff(c_140,plain,(
    ! [A_80,A_81] :
      ( m1_subset_1(A_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ r2_hidden(A_80,u1_pre_topc(A_81))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_20,c_88])).

tff(c_147,plain,(
    ! [A_80,A_81] :
      ( r1_tarski(A_80,u1_struct_0(A_81))
      | ~ r2_hidden(A_80,u1_pre_topc(A_81))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_7119,plain,(
    ! [B_457] :
      ( r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),B_457),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(B_457,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_457,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_7095,c_147])).

tff(c_7315,plain,(
    ! [B_468] :
      ( r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),B_468),u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_468,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_447,c_7119])).

tff(c_38,plain,(
    ! [A_47] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_47),'#skF_1'(A_47)),u1_pre_topc(A_47))
      | v3_tdlat_3(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_769,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3')
    | ~ r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_760,c_38])).

tff(c_781,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3')
    | ~ r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_769])).

tff(c_782,plain,
    ( ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3')
    | ~ r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_781])).

tff(c_845,plain,(
    ~ r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_782])).

tff(c_7340,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_7315,c_845])).

tff(c_7363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2916,c_2841,c_7340])).

tff(c_7365,plain,(
    r1_tarski(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_352,plain,(
    ! [A_119,A_85] :
      ( m1_subset_1(A_119,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_119,u1_struct_0(A_85))
      | ~ m1_pre_topc(A_85,'#skF_3')
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_170,c_346])).

tff(c_363,plain,(
    ! [A_119,A_85] :
      ( m1_subset_1(A_119,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_119,u1_struct_0(A_85))
      | ~ m1_pre_topc(A_85,'#skF_3')
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_352])).

tff(c_14818,plain,(
    ! [A_827,A_828] :
      ( m1_subset_1(A_827,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_827,u1_struct_0(A_828))
      | ~ m1_pre_topc(A_828,'#skF_3')
      | ~ l1_pre_topc(A_828) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_363])).

tff(c_14830,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_7365,c_14818])).

tff(c_14858,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14830])).

tff(c_14973,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14858])).

tff(c_14976,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_14973])).

tff(c_14980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14976])).

tff(c_14982,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14858])).

tff(c_14981,plain,(
    m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_14858])).

tff(c_252,plain,(
    ! [B_100,A_101] :
      ( r2_hidden(B_100,u1_pre_topc(A_101))
      | ~ v3_pre_topc(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_271,plain,(
    ! [A_105,A_106] :
      ( r2_hidden(A_105,u1_pre_topc(A_106))
      | ~ v3_pre_topc(A_105,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ r1_tarski(A_105,u1_struct_0(A_106)) ) ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_10743,plain,(
    ! [A_630,B_631,A_632] :
      ( m1_subset_1(A_630,B_631)
      | ~ r1_tarski(u1_pre_topc(A_632),B_631)
      | ~ v3_pre_topc(A_630,A_632)
      | ~ l1_pre_topc(A_632)
      | ~ r1_tarski(A_630,u1_struct_0(A_632)) ) ),
    inference(resolution,[status(thm)],[c_271,c_94])).

tff(c_10923,plain,(
    ! [A_639,A_640] :
      ( m1_subset_1(A_639,u1_pre_topc(A_640))
      | ~ v3_pre_topc(A_639,A_640)
      | ~ l1_pre_topc(A_640)
      | ~ r1_tarski(A_639,u1_struct_0(A_640)) ) ),
    inference(resolution,[status(thm)],[c_6,c_10743])).

tff(c_10947,plain,(
    ! [A_639] :
      ( m1_subset_1(A_639,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_639,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_639,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_10923])).

tff(c_11003,plain,(
    ! [A_645] :
      ( m1_subset_1(A_645,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(A_645,'#skF_2')
      | ~ r1_tarski(A_645,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10947])).

tff(c_11054,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7365,c_11003])).

tff(c_11079,plain,(
    ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_11054])).

tff(c_7470,plain,(
    ! [B_476] :
      ( r2_hidden(B_476,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_476,'#skF_2')
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_478])).

tff(c_7499,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_7470])).

tff(c_7521,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7499])).

tff(c_7522,plain,
    ( r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_7521])).

tff(c_7525,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7522])).

tff(c_7896,plain,(
    ! [A_494,A_495] :
      ( m1_subset_1(A_494,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_494,u1_struct_0(A_495))
      | ~ m1_pre_topc(A_495,'#skF_3')
      | ~ l1_pre_topc(A_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_363])).

tff(c_7904,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_7365,c_7896])).

tff(c_7927,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7904])).

tff(c_7989,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7927])).

tff(c_7992,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_7989])).

tff(c_7996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7992])).

tff(c_7998,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_7927])).

tff(c_8475,plain,(
    ! [A_517,A_518,A_519] :
      ( m1_subset_1(A_517,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ m1_pre_topc(A_519,A_518)
      | ~ l1_pre_topc(A_518)
      | ~ r2_hidden(A_517,u1_pre_topc(A_519))
      | ~ l1_pre_topc(A_519) ) ),
    inference(resolution,[status(thm)],[c_93,c_296])).

tff(c_8479,plain,(
    ! [A_517] :
      ( m1_subset_1(A_517,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_517,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7998,c_8475])).

tff(c_8513,plain,(
    ! [A_520] :
      ( m1_subset_1(A_520,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_520,u1_pre_topc('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8479])).

tff(c_8544,plain,(
    ! [A_521] :
      ( r1_tarski(A_521,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_521,u1_pre_topc('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8513,c_8])).

tff(c_8569,plain,
    ( r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_8544])).

tff(c_8584,plain,
    ( r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8569])).

tff(c_8585,plain,(
    r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_8584])).

tff(c_8238,plain,(
    ! [A_504,B_505,A_506] :
      ( m1_subset_1(A_504,B_505)
      | ~ r1_tarski(u1_pre_topc(A_506),B_505)
      | ~ v3_pre_topc(A_504,A_506)
      | ~ l1_pre_topc(A_506)
      | ~ r1_tarski(A_504,u1_struct_0(A_506)) ) ),
    inference(resolution,[status(thm)],[c_271,c_94])).

tff(c_8250,plain,(
    ! [A_504,A_506] :
      ( m1_subset_1(A_504,u1_pre_topc(A_506))
      | ~ v3_pre_topc(A_504,A_506)
      | ~ l1_pre_topc(A_506)
      | ~ r1_tarski(A_504,u1_struct_0(A_506)) ) ),
    inference(resolution,[status(thm)],[c_6,c_8238])).

tff(c_8591,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8585,c_8250])).

tff(c_8599,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8591])).

tff(c_8630,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8599])).

tff(c_8646,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_8630])).

tff(c_8649,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8646])).

tff(c_8651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_8649])).

tff(c_8653,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8599])).

tff(c_7895,plain,(
    ! [A_119,A_85] :
      ( m1_subset_1(A_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_119,u1_struct_0(A_85))
      | ~ m1_pre_topc(A_85,'#skF_3')
      | ~ l1_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_363])).

tff(c_8593,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8585,c_7895])).

tff(c_8602,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7998,c_8593])).

tff(c_22,plain,(
    ! [C_21,A_15,B_19] :
      ( m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(B_19)))
      | ~ m1_pre_topc(B_19,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8622,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_pre_topc('#skF_3',A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_8602,c_22])).

tff(c_7442,plain,(
    ! [A_473,C_474,A_475] :
      ( v3_pre_topc(A_473,C_474)
      | ~ v3_pre_topc(A_473,A_475)
      | ~ m1_pre_topc(C_474,A_475)
      | ~ m1_subset_1(A_473,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ l1_pre_topc(A_475)
      | ~ r1_tarski(A_473,u1_struct_0(C_474)) ) ),
    inference(resolution,[status(thm)],[c_10,c_410])).

tff(c_7448,plain,(
    ! [A_473] :
      ( v3_pre_topc(A_473,'#skF_2')
      | ~ v3_pre_topc(A_473,'#skF_3')
      | ~ m1_subset_1(A_473,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_473,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_208,c_7442])).

tff(c_10132,plain,(
    ! [A_607] :
      ( v3_pre_topc(A_607,'#skF_2')
      | ~ v3_pre_topc(A_607,'#skF_3')
      | ~ m1_subset_1(A_607,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_607,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_50,c_7448])).

tff(c_10166,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8622,c_10132])).

tff(c_10233,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7998,c_8585,c_8653,c_10166])).

tff(c_10235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7525,c_10233])).

tff(c_10236,plain,(
    r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7522])).

tff(c_10271,plain,(
    ! [B_608] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_608)
      | ~ r1_tarski(u1_pre_topc('#skF_2'),B_608) ) ),
    inference(resolution,[status(thm)],[c_10236,c_94])).

tff(c_10283,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_544,c_10271])).

tff(c_14672,plain,(
    ! [B_815] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_815),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_815,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_815,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_447,c_462])).

tff(c_487,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_65,u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_93])).

tff(c_619,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_130,u1_pre_topc('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_487])).

tff(c_12273,plain,(
    ! [A_707,A_708] :
      ( m1_subset_1(A_707,k1_zfmisc_1(u1_struct_0(A_708)))
      | ~ m1_pre_topc('#skF_3',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ r2_hidden(A_707,u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_619,c_22])).

tff(c_7364,plain,(
    ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_11115,plain,(
    ! [A_657,A_658] :
      ( m1_subset_1(A_657,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_657,u1_struct_0(A_658))
      | ~ m1_pre_topc(A_658,'#skF_3')
      | ~ l1_pre_topc(A_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_363])).

tff(c_11127,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_7365,c_11115])).

tff(c_11155,plain,
    ( m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11127])).

tff(c_11231,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11155])).

tff(c_11234,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_11231])).

tff(c_11238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11234])).

tff(c_11239,plain,(
    m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_11155])).

tff(c_30,plain,(
    ! [D_42,C_40,A_28] :
      ( v3_pre_topc(D_42,C_40)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(C_40)))
      | ~ v3_pre_topc(D_42,A_28)
      | ~ m1_pre_topc(C_40,A_28)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11327,plain,(
    ! [A_28] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3')
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),A_28)
      | ~ m1_pre_topc('#skF_3',A_28)
      | ~ m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_11239,c_30])).

tff(c_11341,plain,(
    ! [A_28] :
      ( ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),A_28)
      | ~ m1_pre_topc('#skF_3',A_28)
      | ~ m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7364,c_11327])).

tff(c_12297,plain,(
    ! [A_708] :
      ( ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),A_708)
      | ~ m1_pre_topc('#skF_3',A_708)
      | ~ l1_pre_topc(A_708)
      | ~ r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12273,c_11341])).

tff(c_12308,plain,(
    ~ r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12297])).

tff(c_14679,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_14672,c_12308])).

tff(c_14707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10283,c_10236,c_14679])).

tff(c_14709,plain,(
    r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12297])).

tff(c_242,plain,(
    ! [A_65,A_14] :
      ( v3_pre_topc(A_65,A_14)
      | ~ r2_hidden(A_65,u1_pre_topc(A_14))
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_93,c_228])).

tff(c_14729,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14709,c_242])).

tff(c_14749,plain,(
    v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14729])).

tff(c_14751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11079,c_14749])).

tff(c_14753,plain,(
    v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_11054])).

tff(c_15036,plain,(
    ! [A_28] :
      ( v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_3')
      | ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),A_28)
      | ~ m1_pre_topc('#skF_3',A_28)
      | ~ m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_14981,c_30])).

tff(c_15321,plain,(
    ! [A_842] :
      ( ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),A_842)
      | ~ m1_pre_topc('#skF_3',A_842)
      | ~ m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0(A_842)))
      | ~ l1_pre_topc(A_842) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7364,c_15036])).

tff(c_15338,plain,
    ( ~ v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_15321])).

tff(c_15357,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14981,c_14753,c_15338])).

tff(c_15362,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_15357])).

tff(c_15366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14982,c_15362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.74/3.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.58  
% 9.74/3.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.58  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 9.74/3.58  
% 9.74/3.58  %Foreground sorts:
% 9.74/3.58  
% 9.74/3.58  
% 9.74/3.58  %Background operators:
% 9.74/3.58  
% 9.74/3.58  
% 9.74/3.58  %Foreground operators:
% 9.74/3.58  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.74/3.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.74/3.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.74/3.58  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.74/3.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.74/3.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.74/3.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.74/3.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.74/3.58  tff('#skF_2', type, '#skF_2': $i).
% 9.74/3.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.74/3.58  tff('#skF_3', type, '#skF_3': $i).
% 9.74/3.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.74/3.58  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 9.74/3.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.74/3.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.74/3.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.74/3.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.74/3.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.74/3.58  
% 9.74/3.61  tff(f_138, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 9.74/3.61  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.74/3.61  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 9.74/3.61  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 9.74/3.61  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.74/3.61  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.74/3.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.74/3.61  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 9.74/3.61  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 9.74/3.61  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 9.74/3.61  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 9.74/3.61  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 9.74/3.61  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 9.74/3.61  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.74/3.61  tff(c_34, plain, (![A_46]: (m1_pre_topc(A_46, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.74/3.61  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.74/3.61  tff(c_154, plain, (![A_85, B_86]: (m1_pre_topc(A_85, g1_pre_topc(u1_struct_0(B_86), u1_pre_topc(B_86))) | ~m1_pre_topc(A_85, B_86) | ~l1_pre_topc(B_86) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.74/3.61  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.74/3.61  tff(c_119, plain, (![B_75, A_76]: (m1_pre_topc(B_75, A_76) | ~m1_pre_topc(B_75, g1_pre_topc(u1_struct_0(A_76), u1_pre_topc(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.74/3.61  tff(c_122, plain, (![B_75]: (m1_pre_topc(B_75, '#skF_2') | ~m1_pre_topc(B_75, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_119])).
% 9.74/3.61  tff(c_128, plain, (![B_75]: (m1_pre_topc(B_75, '#skF_2') | ~m1_pre_topc(B_75, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_122])).
% 9.74/3.61  tff(c_158, plain, (![A_85]: (m1_pre_topc(A_85, '#skF_2') | ~m1_pre_topc(A_85, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_154, c_128])).
% 9.74/3.61  tff(c_170, plain, (![A_85]: (m1_pre_topc(A_85, '#skF_2') | ~m1_pre_topc(A_85, '#skF_3') | ~l1_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_158])).
% 9.74/3.61  tff(c_111, plain, (![B_73, A_74]: (m1_subset_1(u1_struct_0(B_73), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.74/3.61  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.74/3.61  tff(c_118, plain, (![B_73, A_74]: (r1_tarski(u1_struct_0(B_73), u1_struct_0(A_74)) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_111, c_8])).
% 9.74/3.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.74/3.61  tff(c_167, plain, (![A_85]: (m1_pre_topc(A_85, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_85, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_85))), inference(superposition, [status(thm), theory('equality')], [c_48, c_154])).
% 9.74/3.61  tff(c_182, plain, (![A_88]: (m1_pre_topc(A_88, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_88, '#skF_2') | ~l1_pre_topc(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_167])).
% 9.74/3.61  tff(c_24, plain, (![B_24, A_22]: (m1_pre_topc(B_24, A_22) | ~m1_pre_topc(B_24, g1_pre_topc(u1_struct_0(A_22), u1_pre_topc(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.74/3.61  tff(c_188, plain, (![A_88]: (m1_pre_topc(A_88, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_88, '#skF_2') | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_182, c_24])).
% 9.74/3.61  tff(c_197, plain, (![A_89]: (m1_pre_topc(A_89, '#skF_3') | ~m1_pre_topc(A_89, '#skF_2') | ~l1_pre_topc(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_188])).
% 9.74/3.61  tff(c_204, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_197])).
% 9.74/3.61  tff(c_208, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_204])).
% 9.74/3.61  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.74/3.61  tff(c_296, plain, (![C_111, A_112, B_113]: (m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(B_113))) | ~m1_pre_topc(B_113, A_112) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.74/3.61  tff(c_346, plain, (![A_119, A_120, B_121]: (m1_subset_1(A_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_pre_topc(B_121, A_120) | ~l1_pre_topc(A_120) | ~r1_tarski(A_119, u1_struct_0(B_121)))), inference(resolution, [status(thm)], [c_10, c_296])).
% 9.74/3.61  tff(c_348, plain, (![A_119]: (m1_subset_1(A_119, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_119, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_208, c_346])).
% 9.74/3.61  tff(c_366, plain, (![A_122]: (m1_subset_1(A_122, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_122, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_348])).
% 9.74/3.61  tff(c_383, plain, (![A_123]: (r1_tarski(A_123, u1_struct_0('#skF_3')) | ~r1_tarski(A_123, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_366, c_8])).
% 9.74/3.61  tff(c_402, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_383])).
% 9.74/3.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.74/3.61  tff(c_405, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_402, c_2])).
% 9.74/3.61  tff(c_427, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_405])).
% 9.74/3.61  tff(c_430, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_118, c_427])).
% 9.74/3.61  tff(c_433, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_430])).
% 9.74/3.61  tff(c_436, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_170, c_433])).
% 9.74/3.61  tff(c_439, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_436])).
% 9.74/3.61  tff(c_442, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_439])).
% 9.74/3.61  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_442])).
% 9.74/3.61  tff(c_447, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_405])).
% 9.74/3.61  tff(c_78, plain, (![A_62]: (m1_subset_1(u1_pre_topc(A_62), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.74/3.61  tff(c_82, plain, (![A_62]: (r1_tarski(u1_pre_topc(A_62), k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_78, c_8])).
% 9.74/3.61  tff(c_511, plain, (r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_447, c_82])).
% 9.74/3.61  tff(c_544, plain, (r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_511])).
% 9.74/3.61  tff(c_44, plain, (~v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.74/3.61  tff(c_95, plain, (![A_68]: (m1_subset_1('#skF_1'(A_68), k1_zfmisc_1(u1_struct_0(A_68))) | v3_tdlat_3(A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.74/3.61  tff(c_102, plain, (![A_68]: (r1_tarski('#skF_1'(A_68), u1_struct_0(A_68)) | v3_tdlat_3(A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_95, c_8])).
% 9.74/3.61  tff(c_42, plain, (![A_47]: (m1_subset_1('#skF_1'(A_47), k1_zfmisc_1(u1_struct_0(A_47))) | v3_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.74/3.61  tff(c_16, plain, (![B_10, A_8]: (r2_hidden(B_10, u1_pre_topc(A_8)) | ~v3_pre_topc(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.74/3.61  tff(c_478, plain, (![B_10]: (r2_hidden(B_10, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_10, '#skF_2') | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_447, c_16])).
% 9.74/3.61  tff(c_918, plain, (![B_147]: (r2_hidden(B_147, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_147, '#skF_2') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_478])).
% 9.74/3.61  tff(c_947, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_918])).
% 9.74/3.61  tff(c_969, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_947])).
% 9.74/3.61  tff(c_970, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_969])).
% 9.74/3.61  tff(c_1001, plain, (~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_970])).
% 9.74/3.61  tff(c_40, plain, (![A_47]: (r2_hidden('#skF_1'(A_47), u1_pre_topc(A_47)) | v3_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.74/3.61  tff(c_20, plain, (![A_14]: (m1_subset_1(u1_pre_topc(A_14), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14)))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.74/3.61  tff(c_88, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.74/3.61  tff(c_93, plain, (![A_65, A_14]: (m1_subset_1(A_65, k1_zfmisc_1(u1_struct_0(A_14))) | ~r2_hidden(A_65, u1_pre_topc(A_14)) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_88])).
% 9.74/3.61  tff(c_228, plain, (![B_95, A_96]: (v3_pre_topc(B_95, A_96) | ~r2_hidden(B_95, u1_pre_topc(A_96)) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.74/3.61  tff(c_246, plain, (![A_97, A_98]: (v3_pre_topc(A_97, A_98) | ~r2_hidden(A_97, u1_pre_topc(A_98)) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_93, c_228])).
% 9.74/3.61  tff(c_250, plain, (![A_47]: (v3_pre_topc('#skF_1'(A_47), A_47) | v3_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_40, c_246])).
% 9.74/3.61  tff(c_371, plain, (![A_122]: (r2_hidden(A_122, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_122, '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_122, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_366, c_16])).
% 9.74/3.61  tff(c_380, plain, (![A_122]: (r2_hidden(A_122, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_122, '#skF_3') | ~r1_tarski(A_122, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_371])).
% 9.74/3.61  tff(c_760, plain, (![A_136]: (r2_hidden(A_136, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_136, '#skF_3') | ~r1_tarski(A_136, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_380])).
% 9.74/3.61  tff(c_94, plain, (![A_65, B_4, A_3]: (m1_subset_1(A_65, B_4) | ~r2_hidden(A_65, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_88])).
% 9.74/3.61  tff(c_1621, plain, (![A_185, B_186]: (m1_subset_1(A_185, B_186) | ~r1_tarski(u1_pre_topc('#skF_3'), B_186) | ~v3_pre_topc(A_185, '#skF_3') | ~r1_tarski(A_185, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_760, c_94])).
% 9.74/3.61  tff(c_1632, plain, (![A_187]: (m1_subset_1(A_187, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_187, '#skF_3') | ~r1_tarski(A_187, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_1621])).
% 9.74/3.61  tff(c_1663, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_102, c_1632])).
% 9.74/3.61  tff(c_1684, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1663])).
% 9.74/3.61  tff(c_1685, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_1684])).
% 9.74/3.61  tff(c_1687, plain, (~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1685])).
% 9.74/3.61  tff(c_1718, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_250, c_1687])).
% 9.74/3.61  tff(c_1721, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1718])).
% 9.74/3.61  tff(c_1723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1721])).
% 9.74/3.61  tff(c_1725, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1685])).
% 9.74/3.61  tff(c_410, plain, (![D_125, C_126, A_127]: (v3_pre_topc(D_125, C_126) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(C_126))) | ~v3_pre_topc(D_125, A_127) | ~m1_pre_topc(C_126, A_127) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.74/3.61  tff(c_972, plain, (![A_148, C_149, A_150]: (v3_pre_topc(A_148, C_149) | ~v3_pre_topc(A_148, A_150) | ~m1_pre_topc(C_149, A_150) | ~m1_subset_1(A_148, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~r1_tarski(A_148, u1_struct_0(C_149)))), inference(resolution, [status(thm)], [c_10, c_410])).
% 9.74/3.61  tff(c_978, plain, (![A_148]: (v3_pre_topc(A_148, '#skF_2') | ~v3_pre_topc(A_148, '#skF_3') | ~m1_subset_1(A_148, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_148, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_208, c_972])).
% 9.74/3.61  tff(c_2720, plain, (![A_248]: (v3_pre_topc(A_248, '#skF_2') | ~v3_pre_topc(A_248, '#skF_3') | ~m1_subset_1(A_248, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_248, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_50, c_978])).
% 9.74/3.61  tff(c_2772, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_2720])).
% 9.74/3.61  tff(c_2809, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | ~r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1725, c_2772])).
% 9.74/3.61  tff(c_2810, plain, (~r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1001, c_2809])).
% 9.74/3.61  tff(c_2823, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_102, c_2810])).
% 9.74/3.61  tff(c_2838, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2823])).
% 9.74/3.61  tff(c_2840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2838])).
% 9.74/3.61  tff(c_2841, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_970])).
% 9.74/3.61  tff(c_2904, plain, (![B_252]: (m1_subset_1('#skF_1'('#skF_3'), B_252) | ~r1_tarski(u1_pre_topc('#skF_2'), B_252))), inference(resolution, [status(thm)], [c_2841, c_94])).
% 9.74/3.61  tff(c_2916, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_544, c_2904])).
% 9.74/3.61  tff(c_46, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.74/3.61  tff(c_36, plain, (![A_47, B_50]: (r2_hidden(k6_subset_1(u1_struct_0(A_47), B_50), u1_pre_topc(A_47)) | ~r2_hidden(B_50, u1_pre_topc(A_47)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_47))) | ~v3_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.74/3.61  tff(c_462, plain, (![B_50]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_50), u1_pre_topc('#skF_2')) | ~r2_hidden(B_50, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_447, c_36])).
% 9.74/3.61  tff(c_7095, plain, (![B_457]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_457), u1_pre_topc('#skF_2')) | ~r2_hidden(B_457, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_457, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_447, c_462])).
% 9.74/3.61  tff(c_140, plain, (![A_80, A_81]: (m1_subset_1(A_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~r2_hidden(A_80, u1_pre_topc(A_81)) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_20, c_88])).
% 9.74/3.61  tff(c_147, plain, (![A_80, A_81]: (r1_tarski(A_80, u1_struct_0(A_81)) | ~r2_hidden(A_80, u1_pre_topc(A_81)) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_140, c_8])).
% 9.74/3.61  tff(c_7119, plain, (![B_457]: (r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), B_457), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~r2_hidden(B_457, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_457, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_7095, c_147])).
% 9.74/3.61  tff(c_7315, plain, (![B_468]: (r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), B_468), u1_struct_0('#skF_3')) | ~r2_hidden(B_468, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_447, c_7119])).
% 9.74/3.61  tff(c_38, plain, (![A_47]: (~r2_hidden(k6_subset_1(u1_struct_0(A_47), '#skF_1'(A_47)), u1_pre_topc(A_47)) | v3_tdlat_3(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.74/3.61  tff(c_769, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3') | ~r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_760, c_38])).
% 9.74/3.61  tff(c_781, plain, (v3_tdlat_3('#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3') | ~r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_769])).
% 9.74/3.61  tff(c_782, plain, (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3') | ~r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_781])).
% 9.74/3.61  tff(c_845, plain, (~r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_782])).
% 9.74/3.61  tff(c_7340, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7315, c_845])).
% 9.74/3.61  tff(c_7363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2916, c_2841, c_7340])).
% 9.74/3.61  tff(c_7365, plain, (r1_tarski(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_782])).
% 9.74/3.61  tff(c_352, plain, (![A_119, A_85]: (m1_subset_1(A_119, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_119, u1_struct_0(A_85)) | ~m1_pre_topc(A_85, '#skF_3') | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_170, c_346])).
% 9.74/3.61  tff(c_363, plain, (![A_119, A_85]: (m1_subset_1(A_119, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_119, u1_struct_0(A_85)) | ~m1_pre_topc(A_85, '#skF_3') | ~l1_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_352])).
% 9.74/3.61  tff(c_14818, plain, (![A_827, A_828]: (m1_subset_1(A_827, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_827, u1_struct_0(A_828)) | ~m1_pre_topc(A_828, '#skF_3') | ~l1_pre_topc(A_828))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_363])).
% 9.74/3.61  tff(c_14830, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_7365, c_14818])).
% 9.74/3.61  tff(c_14858, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14830])).
% 9.74/3.61  tff(c_14973, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_14858])).
% 9.74/3.61  tff(c_14976, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_14973])).
% 9.74/3.61  tff(c_14980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_14976])).
% 9.74/3.61  tff(c_14982, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_14858])).
% 9.74/3.61  tff(c_14981, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_14858])).
% 9.74/3.61  tff(c_252, plain, (![B_100, A_101]: (r2_hidden(B_100, u1_pre_topc(A_101)) | ~v3_pre_topc(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.74/3.61  tff(c_271, plain, (![A_105, A_106]: (r2_hidden(A_105, u1_pre_topc(A_106)) | ~v3_pre_topc(A_105, A_106) | ~l1_pre_topc(A_106) | ~r1_tarski(A_105, u1_struct_0(A_106)))), inference(resolution, [status(thm)], [c_10, c_252])).
% 9.74/3.61  tff(c_10743, plain, (![A_630, B_631, A_632]: (m1_subset_1(A_630, B_631) | ~r1_tarski(u1_pre_topc(A_632), B_631) | ~v3_pre_topc(A_630, A_632) | ~l1_pre_topc(A_632) | ~r1_tarski(A_630, u1_struct_0(A_632)))), inference(resolution, [status(thm)], [c_271, c_94])).
% 9.74/3.61  tff(c_10923, plain, (![A_639, A_640]: (m1_subset_1(A_639, u1_pre_topc(A_640)) | ~v3_pre_topc(A_639, A_640) | ~l1_pre_topc(A_640) | ~r1_tarski(A_639, u1_struct_0(A_640)))), inference(resolution, [status(thm)], [c_6, c_10743])).
% 9.74/3.61  tff(c_10947, plain, (![A_639]: (m1_subset_1(A_639, u1_pre_topc('#skF_2')) | ~v3_pre_topc(A_639, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_639, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_447, c_10923])).
% 9.74/3.61  tff(c_11003, plain, (![A_645]: (m1_subset_1(A_645, u1_pre_topc('#skF_2')) | ~v3_pre_topc(A_645, '#skF_2') | ~r1_tarski(A_645, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10947])).
% 9.74/3.61  tff(c_11054, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_7365, c_11003])).
% 9.74/3.61  tff(c_11079, plain, (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_11054])).
% 9.74/3.61  tff(c_7470, plain, (![B_476]: (r2_hidden(B_476, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_476, '#skF_2') | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_478])).
% 9.74/3.61  tff(c_7499, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_7470])).
% 9.74/3.61  tff(c_7521, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7499])).
% 9.74/3.61  tff(c_7522, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_7521])).
% 9.74/3.61  tff(c_7525, plain, (~v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_7522])).
% 9.74/3.61  tff(c_7896, plain, (![A_494, A_495]: (m1_subset_1(A_494, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_494, u1_struct_0(A_495)) | ~m1_pre_topc(A_495, '#skF_3') | ~l1_pre_topc(A_495))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_363])).
% 9.74/3.61  tff(c_7904, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_7365, c_7896])).
% 9.74/3.61  tff(c_7927, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7904])).
% 9.74/3.61  tff(c_7989, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_7927])).
% 9.74/3.61  tff(c_7992, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_7989])).
% 9.74/3.61  tff(c_7996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_7992])).
% 9.74/3.61  tff(c_7998, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_7927])).
% 9.74/3.61  tff(c_8475, plain, (![A_517, A_518, A_519]: (m1_subset_1(A_517, k1_zfmisc_1(u1_struct_0(A_518))) | ~m1_pre_topc(A_519, A_518) | ~l1_pre_topc(A_518) | ~r2_hidden(A_517, u1_pre_topc(A_519)) | ~l1_pre_topc(A_519))), inference(resolution, [status(thm)], [c_93, c_296])).
% 9.74/3.61  tff(c_8479, plain, (![A_517]: (m1_subset_1(A_517, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_517, u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_7998, c_8475])).
% 9.74/3.61  tff(c_8513, plain, (![A_520]: (m1_subset_1(A_520, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_520, u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8479])).
% 9.74/3.61  tff(c_8544, plain, (![A_521]: (r1_tarski(A_521, u1_struct_0('#skF_3')) | ~r2_hidden(A_521, u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_8513, c_8])).
% 9.74/3.61  tff(c_8569, plain, (r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_8544])).
% 9.74/3.61  tff(c_8584, plain, (r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8569])).
% 9.74/3.61  tff(c_8585, plain, (r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_8584])).
% 9.74/3.61  tff(c_8238, plain, (![A_504, B_505, A_506]: (m1_subset_1(A_504, B_505) | ~r1_tarski(u1_pre_topc(A_506), B_505) | ~v3_pre_topc(A_504, A_506) | ~l1_pre_topc(A_506) | ~r1_tarski(A_504, u1_struct_0(A_506)))), inference(resolution, [status(thm)], [c_271, c_94])).
% 9.74/3.61  tff(c_8250, plain, (![A_504, A_506]: (m1_subset_1(A_504, u1_pre_topc(A_506)) | ~v3_pre_topc(A_504, A_506) | ~l1_pre_topc(A_506) | ~r1_tarski(A_504, u1_struct_0(A_506)))), inference(resolution, [status(thm)], [c_6, c_8238])).
% 9.74/3.61  tff(c_8591, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8585, c_8250])).
% 9.74/3.61  tff(c_8599, plain, (m1_subset_1('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8591])).
% 9.74/3.61  tff(c_8630, plain, (~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_8599])).
% 9.74/3.61  tff(c_8646, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_250, c_8630])).
% 9.74/3.61  tff(c_8649, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8646])).
% 9.74/3.61  tff(c_8651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_8649])).
% 9.74/3.61  tff(c_8653, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_8599])).
% 9.74/3.61  tff(c_7895, plain, (![A_119, A_85]: (m1_subset_1(A_119, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_119, u1_struct_0(A_85)) | ~m1_pre_topc(A_85, '#skF_3') | ~l1_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_363])).
% 9.74/3.61  tff(c_8593, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8585, c_7895])).
% 9.74/3.61  tff(c_8602, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7998, c_8593])).
% 9.74/3.61  tff(c_22, plain, (![C_21, A_15, B_19]: (m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(B_19))) | ~m1_pre_topc(B_19, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.74/3.61  tff(c_8622, plain, (![A_15]: (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_pre_topc('#skF_3', A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_8602, c_22])).
% 9.74/3.61  tff(c_7442, plain, (![A_473, C_474, A_475]: (v3_pre_topc(A_473, C_474) | ~v3_pre_topc(A_473, A_475) | ~m1_pre_topc(C_474, A_475) | ~m1_subset_1(A_473, k1_zfmisc_1(u1_struct_0(A_475))) | ~l1_pre_topc(A_475) | ~r1_tarski(A_473, u1_struct_0(C_474)))), inference(resolution, [status(thm)], [c_10, c_410])).
% 9.74/3.61  tff(c_7448, plain, (![A_473]: (v3_pre_topc(A_473, '#skF_2') | ~v3_pre_topc(A_473, '#skF_3') | ~m1_subset_1(A_473, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_473, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_208, c_7442])).
% 9.74/3.61  tff(c_10132, plain, (![A_607]: (v3_pre_topc(A_607, '#skF_2') | ~v3_pre_topc(A_607, '#skF_3') | ~m1_subset_1(A_607, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_607, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_50, c_7448])).
% 9.74/3.61  tff(c_10166, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~r1_tarski('#skF_1'('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8622, c_10132])).
% 9.74/3.61  tff(c_10233, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7998, c_8585, c_8653, c_10166])).
% 9.74/3.61  tff(c_10235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7525, c_10233])).
% 9.74/3.61  tff(c_10236, plain, (r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_7522])).
% 9.74/3.61  tff(c_10271, plain, (![B_608]: (m1_subset_1('#skF_1'('#skF_3'), B_608) | ~r1_tarski(u1_pre_topc('#skF_2'), B_608))), inference(resolution, [status(thm)], [c_10236, c_94])).
% 9.74/3.61  tff(c_10283, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_544, c_10271])).
% 9.74/3.61  tff(c_14672, plain, (![B_815]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_815), u1_pre_topc('#skF_2')) | ~r2_hidden(B_815, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_815, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_447, c_462])).
% 9.74/3.61  tff(c_487, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_65, u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_447, c_93])).
% 9.74/3.61  tff(c_619, plain, (![A_130]: (m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_130, u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_487])).
% 9.74/3.61  tff(c_12273, plain, (![A_707, A_708]: (m1_subset_1(A_707, k1_zfmisc_1(u1_struct_0(A_708))) | ~m1_pre_topc('#skF_3', A_708) | ~l1_pre_topc(A_708) | ~r2_hidden(A_707, u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_619, c_22])).
% 9.74/3.61  tff(c_7364, plain, (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_782])).
% 9.74/3.61  tff(c_11115, plain, (![A_657, A_658]: (m1_subset_1(A_657, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_657, u1_struct_0(A_658)) | ~m1_pre_topc(A_658, '#skF_3') | ~l1_pre_topc(A_658))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_363])).
% 9.74/3.61  tff(c_11127, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_7365, c_11115])).
% 9.74/3.61  tff(c_11155, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_11127])).
% 9.74/3.61  tff(c_11231, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_11155])).
% 9.74/3.61  tff(c_11234, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_11231])).
% 9.74/3.61  tff(c_11238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_11234])).
% 9.74/3.61  tff(c_11239, plain, (m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_11155])).
% 9.74/3.61  tff(c_30, plain, (![D_42, C_40, A_28]: (v3_pre_topc(D_42, C_40) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(C_40))) | ~v3_pre_topc(D_42, A_28) | ~m1_pre_topc(C_40, A_28) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.74/3.61  tff(c_11327, plain, (![A_28]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), A_28) | ~m1_pre_topc('#skF_3', A_28) | ~m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_11239, c_30])).
% 9.74/3.61  tff(c_11341, plain, (![A_28]: (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), A_28) | ~m1_pre_topc('#skF_3', A_28) | ~m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(negUnitSimplification, [status(thm)], [c_7364, c_11327])).
% 9.74/3.61  tff(c_12297, plain, (![A_708]: (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), A_708) | ~m1_pre_topc('#skF_3', A_708) | ~l1_pre_topc(A_708) | ~r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_12273, c_11341])).
% 9.74/3.61  tff(c_12308, plain, (~r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_12297])).
% 9.74/3.61  tff(c_14679, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14672, c_12308])).
% 9.74/3.61  tff(c_14707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10283, c_10236, c_14679])).
% 9.74/3.61  tff(c_14709, plain, (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_12297])).
% 9.74/3.61  tff(c_242, plain, (![A_65, A_14]: (v3_pre_topc(A_65, A_14) | ~r2_hidden(A_65, u1_pre_topc(A_14)) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_93, c_228])).
% 9.74/3.61  tff(c_14729, plain, (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14709, c_242])).
% 9.74/3.61  tff(c_14749, plain, (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14729])).
% 9.74/3.61  tff(c_14751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11079, c_14749])).
% 9.74/3.61  tff(c_14753, plain, (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_11054])).
% 9.74/3.61  tff(c_15036, plain, (![A_28]: (v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_3') | ~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), A_28) | ~m1_pre_topc('#skF_3', A_28) | ~m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_14981, c_30])).
% 9.74/3.61  tff(c_15321, plain, (![A_842]: (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), A_842) | ~m1_pre_topc('#skF_3', A_842) | ~m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0(A_842))) | ~l1_pre_topc(A_842))), inference(negUnitSimplification, [status(thm)], [c_7364, c_15036])).
% 9.74/3.61  tff(c_15338, plain, (~v3_pre_topc(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k6_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_447, c_15321])).
% 9.74/3.61  tff(c_15357, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14981, c_14753, c_15338])).
% 9.74/3.61  tff(c_15362, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_170, c_15357])).
% 9.74/3.61  tff(c_15366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_14982, c_15362])).
% 9.74/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.61  
% 9.74/3.61  Inference rules
% 9.74/3.61  ----------------------
% 9.74/3.61  #Ref     : 0
% 9.74/3.61  #Sup     : 3173
% 9.74/3.61  #Fact    : 0
% 9.74/3.61  #Define  : 0
% 9.74/3.61  #Split   : 41
% 9.74/3.61  #Chain   : 0
% 9.74/3.61  #Close   : 0
% 9.74/3.61  
% 9.74/3.61  Ordering : KBO
% 9.74/3.61  
% 9.74/3.61  Simplification rules
% 9.74/3.61  ----------------------
% 9.74/3.61  #Subsume      : 1211
% 9.74/3.61  #Demod        : 2851
% 9.74/3.61  #Tautology    : 519
% 9.74/3.61  #SimpNegUnit  : 86
% 9.74/3.61  #BackRed      : 3
% 9.74/3.61  
% 9.74/3.61  #Partial instantiations: 0
% 9.74/3.61  #Strategies tried      : 1
% 9.74/3.61  
% 9.74/3.61  Timing (in seconds)
% 9.74/3.61  ----------------------
% 9.74/3.61  Preprocessing        : 0.34
% 9.74/3.61  Parsing              : 0.19
% 9.74/3.61  CNF conversion       : 0.02
% 9.74/3.61  Main loop            : 2.42
% 9.74/3.61  Inferencing          : 0.73
% 9.74/3.61  Reduction            : 0.76
% 9.74/3.61  Demodulation         : 0.49
% 9.74/3.61  BG Simplification    : 0.06
% 10.02/3.61  Subsumption          : 0.69
% 10.02/3.61  Abstraction          : 0.09
% 10.02/3.61  MUC search           : 0.00
% 10.02/3.61  Cooper               : 0.00
% 10.02/3.61  Total                : 2.83
% 10.02/3.61  Index Insertion      : 0.00
% 10.02/3.62  Index Deletion       : 0.00
% 10.02/3.62  Index Matching       : 0.00
% 10.02/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
