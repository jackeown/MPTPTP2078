%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2021+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:46 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  116 (1067 expanded)
%              Number of leaves         :   32 ( 370 expanded)
%              Depth                    :   22
%              Number of atoms          :  228 (2833 expanded)
%              Number of equality atoms :   30 ( 822 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tops_2(C,A) )
                     => v2_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_9)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_38,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    ~ v2_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    ~ v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_72,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_49,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_75,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_49])).

tff(c_702,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1('#skF_1'(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tops_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123))))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_713,plain,(
    ! [B_124] :
      ( m1_subset_1('#skF_1'('#skF_3',B_124),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tops_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_702])).

tff(c_719,plain,(
    ! [B_124] :
      ( m1_subset_1('#skF_1'('#skF_3',B_124),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tops_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_72,c_713])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_73,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_127,plain,(
    ! [A_48] :
      ( m1_subset_1(u1_pre_topc(A_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48))))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_130,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_127])).

tff(c_135,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_130])).

tff(c_40,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_74,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40])).

tff(c_107,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_74])).

tff(c_208,plain,(
    ! [C_73,A_74,D_75,B_76] :
      ( C_73 = A_74
      | g1_pre_topc(C_73,D_75) != g1_pre_topc(A_74,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_212,plain,(
    ! [C_73,D_75] :
      ( k2_struct_0('#skF_2') = C_73
      | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_73,D_75)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_208])).

tff(c_214,plain,(
    ! [C_73,D_75] :
      ( k2_struct_0('#skF_2') = C_73
      | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_73,D_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_212])).

tff(c_217,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_214])).

tff(c_234,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_73])).

tff(c_36,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_564,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_1'(A_112,B_113),B_113)
      | v2_tops_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112))))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_573,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_1'('#skF_3',B_113),B_113)
      | v2_tops_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_564])).

tff(c_616,plain,(
    ! [B_115] :
      ( r2_hidden('#skF_1'('#skF_3',B_115),B_115)
      | v2_tops_2(B_115,'#skF_3')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_573])).

tff(c_623,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v2_tops_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_616])).

tff(c_628,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_623])).

tff(c_842,plain,(
    ! [C_136,A_137,B_138] :
      ( v4_pre_topc(C_136,A_137)
      | ~ r2_hidden(C_136,B_138)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v2_tops_2(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137))))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_893,plain,(
    ! [A_145] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),A_145)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v2_tops_2('#skF_4',A_145)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_628,c_842])).

tff(c_900,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v2_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_893])).

tff(c_913,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_75,c_234,c_36,c_900])).

tff(c_917,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_920,plain,
    ( v2_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_719,c_917])).

tff(c_929,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_920])).

tff(c_931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_929])).

tff(c_932,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_933,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_85,plain,(
    ! [A_47] :
      ( m1_subset_1(k2_struct_0(A_47),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_91,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_85])).

tff(c_112,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_115,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_115])).

tff(c_120,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_637,plain,(
    ! [A_116,B_117] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_116),k2_struct_0(A_116),B_117),A_116)
      | ~ v4_pre_topc(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_647,plain,(
    ! [B_117] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3'),B_117),'#skF_2')
      | ~ v4_pre_topc(B_117,'#skF_2')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_637])).

tff(c_657,plain,(
    ! [B_117] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_117),'#skF_2')
      | ~ v4_pre_topc(B_117,'#skF_2')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_234,c_234,c_647])).

tff(c_230,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_135])).

tff(c_232,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_107])).

tff(c_28,plain,(
    ! [D_29,B_25,C_28,A_24] :
      ( D_29 = B_25
      | g1_pre_topc(C_28,D_29) != g1_pre_topc(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_283,plain,(
    ! [D_29,C_28] :
      ( u1_pre_topc('#skF_2') = D_29
      | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_28,D_29)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_28])).

tff(c_291,plain,(
    ! [D_29,C_28] :
      ( u1_pre_topc('#skF_2') = D_29
      | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_28,D_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_283])).

tff(c_336,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_291])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k7_subset_1(A_19,B_20,C_21),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_301,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,u1_pre_topc(A_85))
      | ~ v3_pre_topc(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1119,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden(k7_subset_1(u1_struct_0(A_167),B_168,C_169),u1_pre_topc(A_167))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_167),B_168,C_169),A_167)
      | ~ l1_pre_topc(A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167))) ) ),
    inference(resolution,[status(thm)],[c_22,c_301])).

tff(c_1144,plain,(
    ! [B_168,C_169] :
      ( r2_hidden(k7_subset_1(k2_struct_0('#skF_3'),B_168,C_169),u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0('#skF_2'),B_168,C_169),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1119])).

tff(c_1272,plain,(
    ! [B_178,C_179] :
      ( r2_hidden(k7_subset_1(k2_struct_0('#skF_3'),B_178,C_179),u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),B_178,C_179),'#skF_2')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_48,c_234,c_336,c_1144])).

tff(c_133,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_127])).

tff(c_137,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_133])).

tff(c_138,plain,(
    ! [A_49,C_50,B_51] :
      ( m1_subset_1(A_49,C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_155,plain,(
    ! [A_49] :
      ( m1_subset_1(A_49,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ r2_hidden(A_49,u1_pre_topc('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_137,c_138])).

tff(c_385,plain,(
    ! [B_92,A_93] :
      ( v3_pre_topc(B_92,A_93)
      | ~ r2_hidden(B_92,u1_pre_topc(A_93))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_401,plain,(
    ! [B_92] :
      ( v3_pre_topc(B_92,'#skF_3')
      | ~ r2_hidden(B_92,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_385])).

tff(c_427,plain,(
    ! [B_98] :
      ( v3_pre_topc(B_98,'#skF_3')
      | ~ r2_hidden(B_98,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_401])).

tff(c_442,plain,(
    ! [A_49] :
      ( v3_pre_topc(A_49,'#skF_3')
      | ~ r2_hidden(A_49,u1_pre_topc('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_155,c_427])).

tff(c_1303,plain,(
    ! [B_180,C_181] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),B_180,C_181),'#skF_3')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),B_180,C_181),'#skF_2')
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1272,c_442])).

tff(c_1309,plain,(
    ! [B_117] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_117),'#skF_3')
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_117,'#skF_2')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_657,c_1303])).

tff(c_1318,plain,(
    ! [B_182] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_182),'#skF_3')
      | ~ v4_pre_topc(B_182,'#skF_2')
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1309])).

tff(c_766,plain,(
    ! [B_128,A_129] :
      ( v4_pre_topc(B_128,A_129)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_129),k2_struct_0(A_129),B_128),A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_782,plain,(
    ! [B_128] :
      ( v4_pre_topc(B_128,'#skF_3')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_128),'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_766])).

tff(c_792,plain,(
    ! [B_128] :
      ( v4_pre_topc(B_128,'#skF_3')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_128),'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_72,c_782])).

tff(c_1327,plain,(
    ! [B_183] :
      ( v4_pre_topc(B_183,'#skF_3')
      | ~ v4_pre_topc(B_183,'#skF_2')
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1318,c_792])).

tff(c_1330,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_933,c_1327])).

tff(c_1352,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_1330])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v4_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1381,plain,
    ( v2_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1352,c_4])).

tff(c_1384,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75,c_72,c_1381])).

tff(c_1386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1384])).

%------------------------------------------------------------------------------
