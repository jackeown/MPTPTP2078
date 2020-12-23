%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:58 EST 2020

% Result     : Theorem 50.21s
% Output     : CNFRefutation 50.68s
% Verified   : 
% Statistics : Number of formulae       :  365 (17780 expanded)
%              Number of leaves         :   44 (5374 expanded)
%              Depth                    :   31
%              Number of atoms          :  991 (57106 expanded)
%              Number of equality atoms :  159 (10871 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_247,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_204,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_197,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_208,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_227,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_215,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_188,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_72,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_44,plain,(
    ! [A_56,B_57] :
      ( l1_pre_topc(k8_tmap_1(A_56,B_57))
      | ~ m1_pre_topc(B_57,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    ! [A_56,B_57] :
      ( v1_pre_topc(k8_tmap_1(A_56,B_57))
      | ~ m1_pre_topc(B_57,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    ! [A_56,B_57] :
      ( v2_pre_topc(k8_tmap_1(A_56,B_57))
      | ~ m1_pre_topc(B_57,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_64,plain,(
    ! [B_72,A_70] :
      ( m1_subset_1(u1_struct_0(B_72),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc(B_72,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46078,plain,(
    ! [A_1080,B_1081] :
      ( k6_tmap_1(A_1080,u1_struct_0(B_1081)) = k8_tmap_1(A_1080,B_1081)
      | ~ m1_subset_1(u1_struct_0(B_1081),k1_zfmisc_1(u1_struct_0(A_1080)))
      | ~ l1_pre_topc(k8_tmap_1(A_1080,B_1081))
      | ~ v2_pre_topc(k8_tmap_1(A_1080,B_1081))
      | ~ v1_pre_topc(k8_tmap_1(A_1080,B_1081))
      | ~ m1_pre_topc(B_1081,A_1080)
      | ~ l1_pre_topc(A_1080)
      | ~ v2_pre_topc(A_1080)
      | v2_struct_0(A_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_49047,plain,(
    ! [A_1144,B_1145] :
      ( k6_tmap_1(A_1144,u1_struct_0(B_1145)) = k8_tmap_1(A_1144,B_1145)
      | ~ l1_pre_topc(k8_tmap_1(A_1144,B_1145))
      | ~ v2_pre_topc(k8_tmap_1(A_1144,B_1145))
      | ~ v1_pre_topc(k8_tmap_1(A_1144,B_1145))
      | ~ v2_pre_topc(A_1144)
      | v2_struct_0(A_1144)
      | ~ m1_pre_topc(B_1145,A_1144)
      | ~ l1_pre_topc(A_1144) ) ),
    inference(resolution,[status(thm)],[c_64,c_46078])).

tff(c_167570,plain,(
    ! [A_2444,B_2445] :
      ( k6_tmap_1(A_2444,u1_struct_0(B_2445)) = k8_tmap_1(A_2444,B_2445)
      | ~ l1_pre_topc(k8_tmap_1(A_2444,B_2445))
      | ~ v1_pre_topc(k8_tmap_1(A_2444,B_2445))
      | ~ m1_pre_topc(B_2445,A_2444)
      | ~ l1_pre_topc(A_2444)
      | ~ v2_pre_topc(A_2444)
      | v2_struct_0(A_2444) ) ),
    inference(resolution,[status(thm)],[c_46,c_49047])).

tff(c_209371,plain,(
    ! [A_2912,B_2913] :
      ( k6_tmap_1(A_2912,u1_struct_0(B_2913)) = k8_tmap_1(A_2912,B_2913)
      | ~ l1_pre_topc(k8_tmap_1(A_2912,B_2913))
      | ~ m1_pre_topc(B_2913,A_2912)
      | ~ l1_pre_topc(A_2912)
      | ~ v2_pre_topc(A_2912)
      | v2_struct_0(A_2912) ) ),
    inference(resolution,[status(thm)],[c_48,c_167570])).

tff(c_209675,plain,(
    ! [A_2916,B_2917] :
      ( k6_tmap_1(A_2916,u1_struct_0(B_2917)) = k8_tmap_1(A_2916,B_2917)
      | ~ m1_pre_topc(B_2917,A_2916)
      | ~ l1_pre_topc(A_2916)
      | ~ v2_pre_topc(A_2916)
      | v2_struct_0(A_2916) ) ),
    inference(resolution,[status(thm)],[c_44,c_209371])).

tff(c_45003,plain,(
    ! [B_940,A_941] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_940),u1_pre_topc(B_940)),A_941)
      | ~ m1_pre_topc(B_940,A_941)
      | ~ l1_pre_topc(A_941) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45019,plain,(
    ! [B_942,A_943] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_942),u1_pre_topc(B_942)))
      | ~ m1_pre_topc(B_942,A_943)
      | ~ l1_pre_topc(A_943) ) ),
    inference(resolution,[status(thm)],[c_45003,c_12])).

tff(c_45025,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_45019])).

tff(c_45030,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_45025])).

tff(c_44976,plain,(
    ! [B_935,A_936] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_935),u1_pre_topc(B_935)))
      | ~ m1_pre_topc(B_935,A_936)
      | ~ l1_pre_topc(A_936) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44980,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_44976])).

tff(c_44984,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_44980])).

tff(c_103,plain,(
    ! [B_90,A_91] :
      ( l1_pre_topc(B_90)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_103])).

tff(c_113,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_109])).

tff(c_14,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_pre_topc(A_10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45063,plain,(
    ! [D_951,B_952,C_953,A_954] :
      ( D_951 = B_952
      | g1_pre_topc(C_953,D_951) != g1_pre_topc(A_954,B_952)
      | ~ m1_subset_1(B_952,k1_zfmisc_1(k1_zfmisc_1(A_954))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_45065,plain,(
    ! [A_3,B_952,A_954] :
      ( u1_pre_topc(A_3) = B_952
      | g1_pre_topc(A_954,B_952) != A_3
      | ~ m1_subset_1(B_952,k1_zfmisc_1(k1_zfmisc_1(A_954)))
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45063])).

tff(c_45432,plain,(
    ! [A_1020,B_1021] :
      ( u1_pre_topc(g1_pre_topc(A_1020,B_1021)) = B_1021
      | ~ m1_subset_1(B_1021,k1_zfmisc_1(k1_zfmisc_1(A_1020)))
      | ~ v1_pre_topc(g1_pre_topc(A_1020,B_1021))
      | ~ l1_pre_topc(g1_pre_topc(A_1020,B_1021)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_45065])).

tff(c_46627,plain,(
    ! [A_1110] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_1110),u1_pre_topc(A_1110))) = u1_pre_topc(A_1110)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_1110),u1_pre_topc(A_1110)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_1110),u1_pre_topc(A_1110)))
      | ~ l1_pre_topc(A_1110) ) ),
    inference(resolution,[status(thm)],[c_14,c_45432])).

tff(c_46651,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44984,c_46627])).

tff(c_46663,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_45030,c_46651])).

tff(c_46809,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46663,c_6])).

tff(c_46903,plain,(
    g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45030,c_44984,c_46809])).

tff(c_66,plain,(
    ! [A_73] :
      ( m1_pre_topc(A_73,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_44994,plain,(
    ! [B_938,A_939] :
      ( m1_pre_topc(B_938,A_939)
      | ~ m1_pre_topc(B_938,g1_pre_topc(u1_struct_0(A_939),u1_pre_topc(A_939)))
      | ~ l1_pre_topc(A_939) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45002,plain,(
    ! [A_939] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_939),u1_pre_topc(A_939)),A_939)
      | ~ l1_pre_topc(A_939)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_939),u1_pre_topc(A_939))) ) ),
    inference(resolution,[status(thm)],[c_66,c_44994])).

tff(c_60,plain,(
    ! [B_69,A_67] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_69),u1_pre_topc(B_69)),A_67)
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_45041,plain,(
    ! [C_947,A_948,B_949] :
      ( m1_pre_topc(C_947,A_948)
      | ~ m1_pre_topc(C_947,B_949)
      | ~ m1_pre_topc(B_949,A_948)
      | ~ l1_pre_topc(A_948)
      | ~ v2_pre_topc(A_948) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_45633,plain,(
    ! [B_1046,A_1047,A_1048] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_1046),u1_pre_topc(B_1046)),A_1047)
      | ~ m1_pre_topc(A_1048,A_1047)
      | ~ l1_pre_topc(A_1047)
      | ~ v2_pre_topc(A_1047)
      | ~ m1_pre_topc(B_1046,A_1048)
      | ~ l1_pre_topc(A_1048) ) ),
    inference(resolution,[status(thm)],[c_60,c_45041])).

tff(c_45641,plain,(
    ! [B_1046] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_1046),u1_pre_topc(B_1046)),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_1046,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_45633])).

tff(c_45647,plain,(
    ! [B_1046] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_1046),u1_pre_topc(B_1046)),'#skF_3')
      | ~ m1_pre_topc(B_1046,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_78,c_76,c_45641])).

tff(c_46755,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')),'#skF_3')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46663,c_45647])).

tff(c_47081,plain,(
    ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46755])).

tff(c_47087,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_45002,c_47081])).

tff(c_47100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45030,c_113,c_47087])).

tff(c_47101,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_46755])).

tff(c_47658,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46903,c_47101])).

tff(c_46818,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46663,c_14])).

tff(c_46909,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45030,c_46818])).

tff(c_22,plain,(
    ! [C_16,A_12,D_17,B_13] :
      ( C_16 = A_12
      | g1_pre_topc(C_16,D_17) != g1_pre_topc(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47691,plain,(
    ! [C_16,D_17] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = C_16
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_16,D_17)
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46903,c_22])).

tff(c_47714,plain,(
    ! [C_16,D_17] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = C_16
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_16,D_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46909,c_47691])).

tff(c_48023,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_47714])).

tff(c_68,plain,(
    ! [B_76,A_74] :
      ( r1_tarski(u1_struct_0(B_76),u1_struct_0(A_74))
      | ~ m1_pre_topc(B_76,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_159075,plain,(
    ! [A_2327] :
      ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(A_2327))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),A_2327)
      | ~ l1_pre_topc(A_2327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48023,c_68])).

tff(c_159088,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_47658,c_159075])).

tff(c_159128,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_159088])).

tff(c_92,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_114,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_82,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_95,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_82])).

tff(c_156,plain,(
    ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_95])).

tff(c_726,plain,(
    ! [A_158,B_159] :
      ( m1_subset_1('#skF_2'(A_158,B_159),k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_tsep_1(B_159,A_158)
      | ~ m1_pre_topc(B_159,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_741,plain,(
    ! [A_158,B_159] :
      ( r1_tarski('#skF_2'(A_158,B_159),u1_struct_0(A_158))
      | v1_tsep_1(B_159,A_158)
      | ~ m1_pre_topc(B_159,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_726,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22307,plain,(
    ! [B_575,A_576] :
      ( r2_hidden(B_575,u1_pre_topc(A_576))
      | k5_tmap_1(A_576,B_575) != u1_pre_topc(A_576)
      | ~ m1_subset_1(B_575,k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576)
      | v2_struct_0(A_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_30685,plain,(
    ! [A_756,A_757] :
      ( r2_hidden(A_756,u1_pre_topc(A_757))
      | k5_tmap_1(A_757,A_756) != u1_pre_topc(A_757)
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757)
      | ~ r1_tarski(A_756,u1_struct_0(A_757)) ) ),
    inference(resolution,[status(thm)],[c_4,c_22307])).

tff(c_439,plain,(
    ! [B_138,A_139] :
      ( u1_struct_0(B_138) = '#skF_2'(A_139,B_138)
      | v1_tsep_1(B_138,A_139)
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_442,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_156])).

tff(c_445,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_442])).

tff(c_463,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc('#skF_4',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_64])).

tff(c_196,plain,(
    ! [B_104,A_105] :
      ( m1_pre_topc(B_104,A_105)
      | ~ m1_pre_topc(B_104,g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_202,plain,(
    ! [B_104] :
      ( m1_pre_topc(B_104,'#skF_3')
      | ~ m1_pre_topc(B_104,k8_tmap_1('#skF_3','#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_196])).

tff(c_210,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_3')
      | ~ m1_pre_topc(B_106,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_202])).

tff(c_215,plain,
    ( m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_210])).

tff(c_216,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_217,plain,(
    ! [B_107,A_108] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_107),u1_pre_topc(B_107)),A_108)
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_241,plain,(
    ! [A_109] :
      ( m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),A_109)
      | ~ m1_pre_topc('#skF_3',A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_217])).

tff(c_254,plain,(
    ! [A_109] :
      ( l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_241,c_12])).

tff(c_261,plain,(
    ! [A_110] :
      ( ~ m1_pre_topc('#skF_3',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_254])).

tff(c_265,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_261])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_265])).

tff(c_271,plain,(
    l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_144,plain,(
    ! [A_95] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_95),u1_pre_topc(A_95)))
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,
    ( v1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_144])).

tff(c_152,plain,
    ( v1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_150])).

tff(c_153,plain,(
    v1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_152])).

tff(c_413,plain,(
    ! [C_122,A_123,D_124,B_125] :
      ( C_122 = A_123
      | g1_pre_topc(C_122,D_124) != g1_pre_topc(A_123,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k1_zfmisc_1(A_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_421,plain,(
    ! [C_122,D_124] :
      ( u1_struct_0('#skF_3') = C_122
      | k8_tmap_1('#skF_3','#skF_4') != g1_pre_topc(C_122,D_124)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_413])).

tff(c_21597,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_21600,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_21597])).

tff(c_21607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_21600])).

tff(c_21628,plain,(
    ! [C_552,D_553] :
      ( u1_struct_0('#skF_3') = C_552
      | k8_tmap_1('#skF_3','#skF_4') != g1_pre_topc(C_552,D_553) ) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_21638,plain,(
    ! [A_554] :
      ( u1_struct_0(A_554) = u1_struct_0('#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != A_554
      | ~ v1_pre_topc(A_554)
      | ~ l1_pre_topc(A_554) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21628])).

tff(c_21653,plain,
    ( u1_struct_0(k8_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_153,c_21638])).

tff(c_21664,plain,(
    u1_struct_0(k8_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_21653])).

tff(c_21742,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))) = k8_tmap_1('#skF_3','#skF_4')
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_6])).

tff(c_21779,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_153,c_21742])).

tff(c_21609,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_427,plain,(
    ! [D_128,B_129,C_130,A_131] :
      ( D_128 = B_129
      | g1_pre_topc(C_130,D_128) != g1_pre_topc(A_131,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k1_zfmisc_1(A_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_435,plain,(
    ! [D_128,C_130] :
      ( u1_pre_topc('#skF_3') = D_128
      | k8_tmap_1('#skF_3','#skF_4') != g1_pre_topc(C_130,D_128)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_427])).

tff(c_21868,plain,(
    ! [D_560,C_561] :
      ( u1_pre_topc('#skF_3') = D_560
      | k8_tmap_1('#skF_3','#skF_4') != g1_pre_topc(C_561,D_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21609,c_435])).

tff(c_21878,plain,(
    u1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) = u1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21779,c_21868])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( v3_pre_topc(B_6,A_4)
      | ~ r2_hidden(B_6,u1_pre_topc(A_4))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_21712,plain,(
    ! [B_6] :
      ( v3_pre_topc(B_6,k8_tmap_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_6,u1_pre_topc(k8_tmap_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_8])).

tff(c_21764,plain,(
    ! [B_6] :
      ( v3_pre_topc(B_6,k8_tmap_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_6,u1_pre_topc(k8_tmap_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_21712])).

tff(c_27215,plain,(
    ! [B_708] :
      ( v3_pre_topc(B_708,k8_tmap_1('#skF_3','#skF_4'))
      | ~ r2_hidden(B_708,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_708,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21878,c_21764])).

tff(c_27237,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_463,c_27215])).

tff(c_27262,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_27237])).

tff(c_27272,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_27262])).

tff(c_30692,plain,
    ( k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30685,c_27272])).

tff(c_30736,plain,
    ( k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_30692])).

tff(c_30737,plain,
    ( k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != u1_pre_topc('#skF_3')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_30736])).

tff(c_30761,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30737])).

tff(c_30764,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_741,c_30761])).

tff(c_30770,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_30764])).

tff(c_30772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_30770])).

tff(c_30773,plain,(
    k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30737])).

tff(c_30774,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30737])).

tff(c_21794,plain,(
    ! [A_557,B_558] :
      ( u1_struct_0(k6_tmap_1(A_557,B_558)) = u1_struct_0(A_557)
      | ~ m1_subset_1(B_558,k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557)
      | v2_struct_0(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_21823,plain,(
    ! [A_557,A_1] :
      ( u1_struct_0(k6_tmap_1(A_557,A_1)) = u1_struct_0(A_557)
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557)
      | v2_struct_0(A_557)
      | ~ r1_tarski(A_1,u1_struct_0(A_557)) ) ),
    inference(resolution,[status(thm)],[c_4,c_21794])).

tff(c_30780,plain,
    ( u1_struct_0(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30774,c_21823])).

tff(c_30787,plain,
    ( u1_struct_0(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_30780])).

tff(c_30788,plain,(
    u1_struct_0(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_30787])).

tff(c_21949,plain,(
    ! [A_562,B_563] :
      ( u1_pre_topc(k6_tmap_1(A_562,B_563)) = k5_tmap_1(A_562,B_563)
      | ~ m1_subset_1(B_563,k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562)
      | v2_struct_0(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_21978,plain,(
    ! [A_562,A_1] :
      ( u1_pre_topc(k6_tmap_1(A_562,A_1)) = k5_tmap_1(A_562,A_1)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562)
      | v2_struct_0(A_562)
      | ~ r1_tarski(A_1,u1_struct_0(A_562)) ) ),
    inference(resolution,[status(thm)],[c_4,c_21949])).

tff(c_30777,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30774,c_21978])).

tff(c_30783,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_30777])).

tff(c_30784,plain,(
    u1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_30783])).

tff(c_168,plain,(
    ! [B_99,A_100] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_99),u1_pre_topc(B_99)))
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_173,plain,(
    ! [A_73] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_73),u1_pre_topc(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_66,c_168])).

tff(c_31159,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))),k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30784,c_173])).

tff(c_31189,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30788,c_31159])).

tff(c_32958,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_31189])).

tff(c_270,plain,(
    m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_158,plain,(
    ! [A_98] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A_98),u1_pre_topc(A_98)))
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_164,plain,
    ( ~ v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_158])).

tff(c_166,plain,
    ( ~ v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_164])).

tff(c_167,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_166])).

tff(c_26333,plain,(
    ! [A_688,A_689] :
      ( u1_struct_0(k6_tmap_1(A_688,A_689)) = u1_struct_0(A_688)
      | ~ l1_pre_topc(A_688)
      | ~ v2_pre_topc(A_688)
      | v2_struct_0(A_688)
      | ~ r1_tarski(A_689,u1_struct_0(A_688)) ) ),
    inference(resolution,[status(thm)],[c_4,c_21794])).

tff(c_26351,plain,(
    ! [A_689] :
      ( u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_3','#skF_4'),A_689)) = u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_689,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_26333])).

tff(c_26372,plain,(
    ! [A_689] :
      ( u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_3','#skF_4'),A_689)) = u1_struct_0('#skF_3')
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_689,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_21664,c_26351])).

tff(c_26373,plain,(
    ! [A_689] :
      ( u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_3','#skF_4'),A_689)) = u1_struct_0('#skF_3')
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_689,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_26372])).

tff(c_26805,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_26373])).

tff(c_26808,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_26805])).

tff(c_26811,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_26808])).

tff(c_26813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_26811])).

tff(c_26815,plain,(
    v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_26373])).

tff(c_26161,plain,(
    ! [A_680,B_681] :
      ( k6_tmap_1(A_680,u1_struct_0(B_681)) = k8_tmap_1(A_680,B_681)
      | ~ m1_subset_1(u1_struct_0(B_681),k1_zfmisc_1(u1_struct_0(A_680)))
      | ~ l1_pre_topc(k8_tmap_1(A_680,B_681))
      | ~ v2_pre_topc(k8_tmap_1(A_680,B_681))
      | ~ v1_pre_topc(k8_tmap_1(A_680,B_681))
      | ~ m1_pre_topc(B_681,A_680)
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38367,plain,(
    ! [A_852,B_853] :
      ( k6_tmap_1(A_852,u1_struct_0(B_853)) = k8_tmap_1(A_852,B_853)
      | ~ l1_pre_topc(k8_tmap_1(A_852,B_853))
      | ~ v2_pre_topc(k8_tmap_1(A_852,B_853))
      | ~ v1_pre_topc(k8_tmap_1(A_852,B_853))
      | ~ v2_pre_topc(A_852)
      | v2_struct_0(A_852)
      | ~ m1_pre_topc(B_853,A_852)
      | ~ l1_pre_topc(A_852) ) ),
    inference(resolution,[status(thm)],[c_64,c_26161])).

tff(c_38370,plain,
    ( k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26815,c_38367])).

tff(c_38376,plain,
    ( k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_78,c_153,c_271,c_445,c_38370])).

tff(c_38377,plain,(
    k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38376])).

tff(c_22154,plain,(
    ! [A_568] :
      ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_568))
      | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),A_568)
      | ~ l1_pre_topc(A_568) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_68])).

tff(c_22160,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_22154])).

tff(c_22165,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_22160])).

tff(c_22217,plain,(
    ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22165])).

tff(c_22246,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_22217])).

tff(c_22253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_22246])).

tff(c_22255,plain,(
    m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22165])).

tff(c_22168,plain,(
    ! [B_569,A_570] :
      ( v3_pre_topc(u1_struct_0(B_569),A_570)
      | ~ m1_subset_1(u1_struct_0(B_569),k1_zfmisc_1(u1_struct_0(A_570)))
      | ~ v1_tsep_1(B_569,A_570)
      | ~ m1_pre_topc(B_569,A_570)
      | ~ l1_pre_topc(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22205,plain,(
    ! [B_72,A_70] :
      ( v3_pre_topc(u1_struct_0(B_72),A_70)
      | ~ v1_tsep_1(B_72,A_70)
      | ~ m1_pre_topc(B_72,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_64,c_22168])).

tff(c_22254,plain,(
    r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22165])).

tff(c_585,plain,(
    ! [B_146,A_147] :
      ( r2_hidden(B_146,u1_pre_topc(A_147))
      | ~ v3_pre_topc(B_146,A_147)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_599,plain,(
    ! [A_1,A_147] :
      ( r2_hidden(A_1,u1_pre_topc(A_147))
      | ~ v3_pre_topc(A_1,A_147)
      | ~ l1_pre_topc(A_147)
      | ~ r1_tarski(A_1,u1_struct_0(A_147)) ) ),
    inference(resolution,[status(thm)],[c_4,c_585])).

tff(c_21730,plain,(
    ! [B_72] :
      ( m1_subset_1(u1_struct_0(B_72),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_72,k8_tmap_1('#skF_3','#skF_4'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_64])).

tff(c_21772,plain,(
    ! [B_72] :
      ( m1_subset_1(u1_struct_0(B_72),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_72,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_21730])).

tff(c_22493,plain,(
    ! [A_581,B_582] :
      ( k5_tmap_1(A_581,B_582) = u1_pre_topc(A_581)
      | ~ r2_hidden(B_582,u1_pre_topc(A_581))
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ l1_pre_topc(A_581)
      | ~ v2_pre_topc(A_581)
      | v2_struct_0(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_22499,plain,(
    ! [B_72] :
      ( k5_tmap_1('#skF_3',u1_struct_0(B_72)) = u1_pre_topc('#skF_3')
      | ~ r2_hidden(u1_struct_0(B_72),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_72,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_21772,c_22493])).

tff(c_22521,plain,(
    ! [B_72] :
      ( k5_tmap_1('#skF_3',u1_struct_0(B_72)) = u1_pre_topc('#skF_3')
      | ~ r2_hidden(u1_struct_0(B_72),u1_pre_topc('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_72,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_22499])).

tff(c_22549,plain,(
    ! [B_584] :
      ( k5_tmap_1('#skF_3',u1_struct_0(B_584)) = u1_pre_topc('#skF_3')
      | ~ r2_hidden(u1_struct_0(B_584),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_584,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_22521])).

tff(c_22555,plain,
    ( k5_tmap_1('#skF_3',u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) = u1_pre_topc('#skF_3')
    | ~ r2_hidden(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_22549])).

tff(c_22563,plain,
    ( k5_tmap_1('#skF_3',u1_struct_0('#skF_3')) = u1_pre_topc('#skF_3')
    | ~ r2_hidden(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22255,c_21664,c_22555])).

tff(c_22568,plain,(
    ~ r2_hidden(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22563])).

tff(c_22571,plain,
    ( ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_599,c_22568])).

tff(c_22574,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22254,c_76,c_22571])).

tff(c_22577,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22205,c_22574])).

tff(c_22580,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22577])).

tff(c_22581,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22580])).

tff(c_22584,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_22581])).

tff(c_22588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22584])).

tff(c_22590,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22580])).

tff(c_38,plain,(
    ! [B_49,A_43] :
      ( u1_struct_0(B_49) = '#skF_2'(A_43,B_49)
      | v1_tsep_1(B_49,A_43)
      | ~ m1_pre_topc(B_49,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22589,plain,(
    ~ v1_tsep_1('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22580])).

tff(c_22650,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_22589])).

tff(c_22653,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22590,c_22650])).

tff(c_22712,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22653,c_463])).

tff(c_22793,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_22712])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( r2_hidden(B_6,u1_pre_topc(A_4))
      | ~ v3_pre_topc(B_6,A_4)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22718,plain,(
    ! [B_6] :
      ( r2_hidden(B_6,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_6,'#skF_3')
      | ~ m1_subset_1(B_6,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22653,c_10])).

tff(c_24714,plain,(
    ! [B_632] :
      ( r2_hidden(B_632,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_632,'#skF_3')
      | ~ m1_subset_1(B_632,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22718])).

tff(c_24735,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22793,c_24714])).

tff(c_24737,plain,(
    ~ v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24735])).

tff(c_22727,plain,(
    ! [B_6] :
      ( v3_pre_topc(B_6,'#skF_3')
      | ~ r2_hidden(B_6,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_6,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22653,c_8])).

tff(c_24926,plain,(
    ! [B_637] :
      ( v3_pre_topc(B_637,'#skF_3')
      | ~ r2_hidden(B_637,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_637,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_22727])).

tff(c_24938,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22793,c_24926])).

tff(c_24949,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_24737,c_24938])).

tff(c_52,plain,(
    ! [B_63,A_61] :
      ( r2_hidden(B_63,u1_pre_topc(A_61))
      | k5_tmap_1(A_61,B_63) != u1_pre_topc(A_61)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_22686,plain,(
    ! [B_63] :
      ( r2_hidden(B_63,u1_pre_topc('#skF_3'))
      | k5_tmap_1('#skF_3',B_63) != u1_pre_topc('#skF_3')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22653,c_52])).

tff(c_22776,plain,(
    ! [B_63] :
      ( r2_hidden(B_63,u1_pre_topc('#skF_3'))
      | k5_tmap_1('#skF_3',B_63) != u1_pre_topc('#skF_3')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_22686])).

tff(c_23534,plain,(
    ! [B_607] :
      ( r2_hidden(B_607,u1_pre_topc('#skF_3'))
      | k5_tmap_1('#skF_3',B_607) != u1_pre_topc('#skF_3')
      | ~ m1_subset_1(B_607,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_22776])).

tff(c_23552,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3'))
    | k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != u1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22793,c_23534])).

tff(c_25121,plain,(
    k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != u1_pre_topc('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24949,c_23552])).

tff(c_23314,plain,(
    ! [A_603,B_604] :
      ( k6_tmap_1(A_603,u1_struct_0(B_604)) = k8_tmap_1(A_603,B_604)
      | ~ m1_subset_1(u1_struct_0(B_604),k1_zfmisc_1(u1_struct_0(A_603)))
      | ~ l1_pre_topc(k8_tmap_1(A_603,B_604))
      | ~ v2_pre_topc(k8_tmap_1(A_603,B_604))
      | ~ v1_pre_topc(k8_tmap_1(A_603,B_604))
      | ~ m1_pre_topc(B_604,A_603)
      | ~ l1_pre_topc(A_603)
      | ~ v2_pre_topc(A_603)
      | v2_struct_0(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_23332,plain,(
    ! [B_604] :
      ( k6_tmap_1('#skF_3',u1_struct_0(B_604)) = k8_tmap_1('#skF_3',B_604)
      | ~ m1_subset_1(u1_struct_0(B_604),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3',B_604))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3',B_604))
      | ~ v1_pre_topc(k8_tmap_1('#skF_3',B_604))
      | ~ m1_pre_topc(B_604,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22653,c_23314])).

tff(c_23352,plain,(
    ! [B_604] :
      ( k6_tmap_1('#skF_3',u1_struct_0(B_604)) = k8_tmap_1('#skF_3',B_604)
      | ~ m1_subset_1(u1_struct_0(B_604),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3',B_604))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3',B_604))
      | ~ v1_pre_topc(k8_tmap_1('#skF_3',B_604))
      | ~ m1_pre_topc(B_604,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_23332])).

tff(c_25351,plain,(
    ! [B_648] :
      ( k6_tmap_1('#skF_3',u1_struct_0(B_648)) = k8_tmap_1('#skF_3',B_648)
      | ~ m1_subset_1(u1_struct_0(B_648),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3',B_648))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3',B_648))
      | ~ v1_pre_topc(k8_tmap_1('#skF_3',B_648))
      | ~ m1_pre_topc(B_648,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_23352])).

tff(c_25381,plain,
    ( k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_25351])).

tff(c_25400,plain,
    ( k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_153,c_271,c_22793,c_445,c_25381])).

tff(c_25402,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_25400])).

tff(c_25405,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_25402])).

tff(c_25408,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_25405])).

tff(c_25410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_25408])).

tff(c_25411,plain,(
    k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_25400])).

tff(c_56,plain,(
    ! [A_64,B_66] :
      ( u1_pre_topc(k6_tmap_1(A_64,B_66)) = k5_tmap_1(A_64,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_22698,plain,(
    ! [B_66] :
      ( u1_pre_topc(k6_tmap_1('#skF_3',B_66)) = k5_tmap_1('#skF_3',B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22653,c_56])).

tff(c_22781,plain,(
    ! [B_66] :
      ( u1_pre_topc(k6_tmap_1('#skF_3',B_66)) = k5_tmap_1('#skF_3',B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_22698])).

tff(c_23020,plain,(
    ! [B_594] :
      ( u1_pre_topc(k6_tmap_1('#skF_3',B_594)) = k5_tmap_1('#skF_3',B_594)
      | ~ m1_subset_1(B_594,k1_zfmisc_1('#skF_2'('#skF_3','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_22781])).

tff(c_23028,plain,(
    u1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22793,c_23020])).

tff(c_25418,plain,(
    k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = u1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25411,c_23028])).

tff(c_25420,plain,(
    k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21878,c_25418])).

tff(c_25422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25121,c_25420])).

tff(c_25424,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_24735])).

tff(c_36,plain,(
    ! [A_43,B_49] :
      ( ~ v3_pre_topc('#skF_2'(A_43,B_49),A_43)
      | v1_tsep_1(B_49,A_43)
      | ~ m1_pre_topc(B_49,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_25427,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_25424,c_36])).

tff(c_25430,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_25427])).

tff(c_25432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_25430])).

tff(c_25433,plain,(
    k5_tmap_1('#skF_3',u1_struct_0('#skF_3')) = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_22563])).

tff(c_25435,plain,(
    ! [A_649,B_650] :
      ( g1_pre_topc(u1_struct_0(A_649),k5_tmap_1(A_649,B_650)) = k6_tmap_1(A_649,B_650)
      | ~ m1_subset_1(B_650,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ l1_pre_topc(A_649)
      | ~ v2_pre_topc(A_649)
      | v2_struct_0(A_649) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_25439,plain,(
    ! [B_72] :
      ( g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3',u1_struct_0(B_72))) = k6_tmap_1('#skF_3',u1_struct_0(B_72))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_72,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_21772,c_25435])).

tff(c_25455,plain,(
    ! [B_72] :
      ( g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3',u1_struct_0(B_72))) = k6_tmap_1('#skF_3',u1_struct_0(B_72))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_72,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_25439])).

tff(c_25488,plain,(
    ! [B_651] :
      ( g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3',u1_struct_0(B_651))) = k6_tmap_1('#skF_3',u1_struct_0(B_651))
      | ~ m1_pre_topc(B_651,k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_25455])).

tff(c_25517,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3',u1_struct_0('#skF_3'))) = k6_tmap_1('#skF_3',u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_25488])).

tff(c_25527,plain,(
    k6_tmap_1('#skF_3',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22255,c_114,c_25433,c_21664,c_25517])).

tff(c_25596,plain,(
    ! [A_655] :
      ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_655)))
      | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),A_655)
      | ~ l1_pre_topc(A_655) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_64])).

tff(c_25627,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_25596])).

tff(c_25641,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_22255,c_25627])).

tff(c_26164,plain,
    ( k6_tmap_1('#skF_3',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_3','#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_25641,c_26161])).

tff(c_26197,plain,
    ( k8_tmap_1('#skF_3','#skF_3') = k8_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_25527,c_26164])).

tff(c_26198,plain,
    ( k8_tmap_1('#skF_3','#skF_3') = k8_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_26197])).

tff(c_26245,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26198])).

tff(c_26248,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_26245])).

tff(c_26252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26248])).

tff(c_26254,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26198])).

tff(c_370,plain,(
    ! [C_117,A_118,B_119] :
      ( m1_pre_topc(C_117,A_118)
      | ~ m1_pre_topc(C_117,B_119)
      | ~ m1_pre_topc(B_119,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_31598,plain,(
    ! [B_765,A_766,A_767] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_765),u1_pre_topc(B_765)),A_766)
      | ~ m1_pre_topc(A_767,A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | ~ m1_pre_topc(B_765,A_767)
      | ~ l1_pre_topc(A_767) ) ),
    inference(resolution,[status(thm)],[c_60,c_370])).

tff(c_31602,plain,(
    ! [B_765] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_765),u1_pre_topc(B_765)),'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_765,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26254,c_31598])).

tff(c_31998,plain,(
    ! [B_772] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_772),u1_pre_topc(B_772)),'#skF_3')
      | ~ m1_pre_topc(B_772,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_31602])).

tff(c_32013,plain,(
    ! [B_772] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_772),u1_pre_topc(B_772)))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_772,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_31998,c_12])).

tff(c_32100,plain,(
    ! [B_773] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_773),u1_pre_topc(B_773)))
      | ~ m1_pre_topc(B_773,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_32013])).

tff(c_32103,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))),k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))))
    | ~ m1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30784,c_32100])).

tff(c_32158,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))))
    | ~ m1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30788,c_32103])).

tff(c_33275,plain,(
    ~ m1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32158])).

tff(c_38379,plain,(
    ~ m1_pre_topc(k8_tmap_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38377,c_33275])).

tff(c_38388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_38379])).

tff(c_38390,plain,(
    m1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32158])).

tff(c_38405,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38390,c_12])).

tff(c_38424,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_38405])).

tff(c_38426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32958,c_38424])).

tff(c_38428,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_31189])).

tff(c_25466,plain,(
    ! [A_649,A_1] :
      ( g1_pre_topc(u1_struct_0(A_649),k5_tmap_1(A_649,A_1)) = k6_tmap_1(A_649,A_1)
      | ~ l1_pre_topc(A_649)
      | ~ v2_pre_topc(A_649)
      | v2_struct_0(A_649)
      | ~ r1_tarski(A_1,u1_struct_0(A_649)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25435])).

tff(c_38427,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_31189])).

tff(c_38439,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25466,c_38427])).

tff(c_38443,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30774,c_78,c_76,c_38439])).

tff(c_38444,plain,(
    v1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38443])).

tff(c_21874,plain,(
    ! [A_3] :
      ( u1_pre_topc(A_3) = u1_pre_topc('#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21868])).

tff(c_38447,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_pre_topc('#skF_3')
    | k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_38444,c_21874])).

tff(c_38453,plain,
    ( k5_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = u1_pre_topc('#skF_3')
    | k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38428,c_30784,c_38447])).

tff(c_38454,plain,(
    k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30773,c_38453])).

tff(c_44903,plain,(
    ! [A_924,B_925] :
      ( k6_tmap_1(A_924,u1_struct_0(B_925)) = k8_tmap_1(A_924,B_925)
      | ~ l1_pre_topc(k8_tmap_1(A_924,B_925))
      | ~ v2_pre_topc(k8_tmap_1(A_924,B_925))
      | ~ v1_pre_topc(k8_tmap_1(A_924,B_925))
      | ~ v2_pre_topc(A_924)
      | v2_struct_0(A_924)
      | ~ m1_pre_topc(B_925,A_924)
      | ~ l1_pre_topc(A_924) ) ),
    inference(resolution,[status(thm)],[c_64,c_26161])).

tff(c_44906,plain,
    ( k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26815,c_44903])).

tff(c_44912,plain,
    ( k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_78,c_153,c_271,c_445,c_44906])).

tff(c_44914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38454,c_44912])).

tff(c_44916,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27262])).

tff(c_514,plain,(
    ! [B_140,A_141] :
      ( v3_pre_topc(B_140,A_141)
      | ~ r2_hidden(B_140,u1_pre_topc(A_141))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25799,plain,(
    ! [B_661,A_662] :
      ( v3_pre_topc(u1_struct_0(B_661),A_662)
      | ~ r2_hidden(u1_struct_0(B_661),u1_pre_topc(A_662))
      | ~ m1_pre_topc(B_661,A_662)
      | ~ l1_pre_topc(A_662) ) ),
    inference(resolution,[status(thm)],[c_64,c_514])).

tff(c_25834,plain,(
    ! [A_662] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),A_662)
      | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc(A_662))
      | ~ m1_pre_topc('#skF_4',A_662)
      | ~ l1_pre_topc(A_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_25799])).

tff(c_25852,plain,(
    ! [A_662] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),A_662)
      | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc(A_662))
      | ~ m1_pre_topc('#skF_4',A_662)
      | ~ l1_pre_topc(A_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_25834])).

tff(c_44919,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44916,c_25852])).

tff(c_44925,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_44919])).

tff(c_44931,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44925,c_36])).

tff(c_44934,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_44931])).

tff(c_44936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_44934])).

tff(c_44937,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_45298,plain,(
    ! [B_1002,A_1003] :
      ( v3_pre_topc(u1_struct_0(B_1002),A_1003)
      | ~ m1_subset_1(u1_struct_0(B_1002),k1_zfmisc_1(u1_struct_0(A_1003)))
      | ~ v1_tsep_1(B_1002,A_1003)
      | ~ m1_pre_topc(B_1002,A_1003)
      | ~ l1_pre_topc(A_1003) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_45311,plain,(
    ! [B_72,A_70] :
      ( v3_pre_topc(u1_struct_0(B_72),A_70)
      | ~ v1_tsep_1(B_72,A_70)
      | ~ m1_pre_topc(B_72,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_64,c_45298])).

tff(c_45081,plain,(
    ! [B_967,A_968] :
      ( r2_hidden(B_967,u1_pre_topc(A_968))
      | ~ v3_pre_topc(B_967,A_968)
      | ~ m1_subset_1(B_967,k1_zfmisc_1(u1_struct_0(A_968)))
      | ~ l1_pre_topc(A_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45090,plain,(
    ! [A_1,A_968] :
      ( r2_hidden(A_1,u1_pre_topc(A_968))
      | ~ v3_pre_topc(A_1,A_968)
      | ~ l1_pre_topc(A_968)
      | ~ r1_tarski(A_1,u1_struct_0(A_968)) ) ),
    inference(resolution,[status(thm)],[c_4,c_45081])).

tff(c_45475,plain,(
    ! [A_1030,B_1031] :
      ( k5_tmap_1(A_1030,B_1031) = u1_pre_topc(A_1030)
      | ~ r2_hidden(B_1031,u1_pre_topc(A_1030))
      | ~ m1_subset_1(B_1031,k1_zfmisc_1(u1_struct_0(A_1030)))
      | ~ l1_pre_topc(A_1030)
      | ~ v2_pre_topc(A_1030)
      | v2_struct_0(A_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_45988,plain,(
    ! [A_1072,A_1073] :
      ( k5_tmap_1(A_1072,A_1073) = u1_pre_topc(A_1072)
      | ~ r2_hidden(A_1073,u1_pre_topc(A_1072))
      | ~ l1_pre_topc(A_1072)
      | ~ v2_pre_topc(A_1072)
      | v2_struct_0(A_1072)
      | ~ r1_tarski(A_1073,u1_struct_0(A_1072)) ) ),
    inference(resolution,[status(thm)],[c_4,c_45475])).

tff(c_46003,plain,(
    ! [A_968,A_1] :
      ( k5_tmap_1(A_968,A_1) = u1_pre_topc(A_968)
      | ~ v2_pre_topc(A_968)
      | v2_struct_0(A_968)
      | ~ v3_pre_topc(A_1,A_968)
      | ~ l1_pre_topc(A_968)
      | ~ r1_tarski(A_1,u1_struct_0(A_968)) ) ),
    inference(resolution,[status(thm)],[c_45090,c_45988])).

tff(c_159150,plain,
    ( k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) = u1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_159128,c_46003])).

tff(c_159162,plain,
    ( k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) = u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_159150])).

tff(c_159163,plain,
    ( k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) = u1_pre_topc('#skF_3')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_159162])).

tff(c_159683,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_159163])).

tff(c_159689,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_45311,c_159683])).

tff(c_159697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_44937,c_159689])).

tff(c_159698,plain,(
    k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_159163])).

tff(c_45334,plain,(
    ! [B_1008,A_1009] :
      ( r2_hidden(B_1008,u1_pre_topc(A_1009))
      | k5_tmap_1(A_1009,B_1008) != u1_pre_topc(A_1009)
      | ~ m1_subset_1(B_1008,k1_zfmisc_1(u1_struct_0(A_1009)))
      | ~ l1_pre_topc(A_1009)
      | ~ v2_pre_topc(A_1009)
      | v2_struct_0(A_1009) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_45520,plain,(
    ! [A_1034,A_1035] :
      ( r2_hidden(A_1034,u1_pre_topc(A_1035))
      | k5_tmap_1(A_1035,A_1034) != u1_pre_topc(A_1035)
      | ~ l1_pre_topc(A_1035)
      | ~ v2_pre_topc(A_1035)
      | v2_struct_0(A_1035)
      | ~ r1_tarski(A_1034,u1_struct_0(A_1035)) ) ),
    inference(resolution,[status(thm)],[c_4,c_45334])).

tff(c_45091,plain,(
    ! [B_969,A_970] :
      ( v3_pre_topc(B_969,A_970)
      | ~ r2_hidden(B_969,u1_pre_topc(A_970))
      | ~ m1_subset_1(B_969,k1_zfmisc_1(u1_struct_0(A_970)))
      | ~ l1_pre_topc(A_970) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45100,plain,(
    ! [A_1,A_970] :
      ( v3_pre_topc(A_1,A_970)
      | ~ r2_hidden(A_1,u1_pre_topc(A_970))
      | ~ l1_pre_topc(A_970)
      | ~ r1_tarski(A_1,u1_struct_0(A_970)) ) ),
    inference(resolution,[status(thm)],[c_4,c_45091])).

tff(c_45532,plain,(
    ! [A_1034,A_1035] :
      ( v3_pre_topc(A_1034,A_1035)
      | k5_tmap_1(A_1035,A_1034) != u1_pre_topc(A_1035)
      | ~ l1_pre_topc(A_1035)
      | ~ v2_pre_topc(A_1035)
      | v2_struct_0(A_1035)
      | ~ r1_tarski(A_1034,u1_struct_0(A_1035)) ) ),
    inference(resolution,[status(thm)],[c_45520,c_45100])).

tff(c_159153,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3')
    | k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) != u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_159128,c_45532])).

tff(c_159166,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3')
    | k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) != u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_159153])).

tff(c_159167,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_3')
    | k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) != u1_pre_topc('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_159166])).

tff(c_159682,plain,(
    k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) != u1_pre_topc('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_159167])).

tff(c_159804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159698,c_159682])).

tff(c_159806,plain,(
    k5_tmap_1('#skF_3',u1_struct_0('#skF_4')) = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_159167])).

tff(c_45442,plain,(
    ! [A_1022,B_1023] :
      ( g1_pre_topc(u1_struct_0(A_1022),k5_tmap_1(A_1022,B_1023)) = k6_tmap_1(A_1022,B_1023)
      | ~ m1_subset_1(B_1023,k1_zfmisc_1(u1_struct_0(A_1022)))
      | ~ l1_pre_topc(A_1022)
      | ~ v2_pre_topc(A_1022)
      | v2_struct_0(A_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_45454,plain,(
    ! [A_1022,A_1] :
      ( g1_pre_topc(u1_struct_0(A_1022),k5_tmap_1(A_1022,A_1)) = k6_tmap_1(A_1022,A_1)
      | ~ l1_pre_topc(A_1022)
      | ~ v2_pre_topc(A_1022)
      | v2_struct_0(A_1022)
      | ~ r1_tarski(A_1,u1_struct_0(A_1022)) ) ),
    inference(resolution,[status(thm)],[c_4,c_45442])).

tff(c_159827,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159806,c_45454])).

tff(c_159850,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159128,c_78,c_76,c_159827])).

tff(c_159851,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_159850])).

tff(c_44938,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_160096,plain,(
    k6_tmap_1('#skF_3',u1_struct_0('#skF_4')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159851,c_44938])).

tff(c_210377,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_209675,c_160096])).

tff(c_210926,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_210377])).

tff(c_210928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_210926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.21/35.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.37/35.52  
% 50.37/35.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.37/35.52  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 50.37/35.52  
% 50.37/35.52  %Foreground sorts:
% 50.37/35.52  
% 50.37/35.52  
% 50.37/35.52  %Background operators:
% 50.37/35.52  
% 50.37/35.52  
% 50.37/35.52  %Foreground operators:
% 50.37/35.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 50.37/35.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 50.37/35.52  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 50.37/35.52  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 50.37/35.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.37/35.52  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 50.37/35.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.37/35.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 50.37/35.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 50.37/35.52  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 50.37/35.52  tff('#skF_3', type, '#skF_3': $i).
% 50.37/35.52  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 50.37/35.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 50.37/35.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.37/35.52  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 50.37/35.52  tff('#skF_4', type, '#skF_4': $i).
% 50.37/35.52  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 50.37/35.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.37/35.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 50.37/35.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 50.37/35.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 50.37/35.52  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 50.37/35.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 50.37/35.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 50.37/35.52  
% 50.68/35.57  tff(f_247, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 50.68/35.57  tff(f_148, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 50.68/35.57  tff(f_204, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 50.68/35.57  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 50.68/35.57  tff(f_197, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 50.68/35.57  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 50.68/35.57  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 50.68/35.57  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 50.68/35.57  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 50.68/35.57  tff(f_208, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 50.68/35.57  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 50.68/35.57  tff(f_227, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 50.68/35.57  tff(f_215, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 50.68/35.57  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 50.68/35.57  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 50.68/35.57  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 50.68/35.57  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 50.68/35.57  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 50.68/35.57  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 50.68/35.57  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 50.68/35.57  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 50.68/35.57  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 50.68/35.57  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 50.68/35.57  tff(c_72, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 50.68/35.57  tff(c_44, plain, (![A_56, B_57]: (l1_pre_topc(k8_tmap_1(A_56, B_57)) | ~m1_pre_topc(B_57, A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_148])).
% 50.68/35.57  tff(c_48, plain, (![A_56, B_57]: (v1_pre_topc(k8_tmap_1(A_56, B_57)) | ~m1_pre_topc(B_57, A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_148])).
% 50.68/35.57  tff(c_46, plain, (![A_56, B_57]: (v2_pre_topc(k8_tmap_1(A_56, B_57)) | ~m1_pre_topc(B_57, A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_148])).
% 50.68/35.57  tff(c_64, plain, (![B_72, A_70]: (m1_subset_1(u1_struct_0(B_72), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc(B_72, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_204])).
% 50.68/35.57  tff(c_46078, plain, (![A_1080, B_1081]: (k6_tmap_1(A_1080, u1_struct_0(B_1081))=k8_tmap_1(A_1080, B_1081) | ~m1_subset_1(u1_struct_0(B_1081), k1_zfmisc_1(u1_struct_0(A_1080))) | ~l1_pre_topc(k8_tmap_1(A_1080, B_1081)) | ~v2_pre_topc(k8_tmap_1(A_1080, B_1081)) | ~v1_pre_topc(k8_tmap_1(A_1080, B_1081)) | ~m1_pre_topc(B_1081, A_1080) | ~l1_pre_topc(A_1080) | ~v2_pre_topc(A_1080) | v2_struct_0(A_1080))), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.68/35.57  tff(c_49047, plain, (![A_1144, B_1145]: (k6_tmap_1(A_1144, u1_struct_0(B_1145))=k8_tmap_1(A_1144, B_1145) | ~l1_pre_topc(k8_tmap_1(A_1144, B_1145)) | ~v2_pre_topc(k8_tmap_1(A_1144, B_1145)) | ~v1_pre_topc(k8_tmap_1(A_1144, B_1145)) | ~v2_pre_topc(A_1144) | v2_struct_0(A_1144) | ~m1_pre_topc(B_1145, A_1144) | ~l1_pre_topc(A_1144))), inference(resolution, [status(thm)], [c_64, c_46078])).
% 50.68/35.57  tff(c_167570, plain, (![A_2444, B_2445]: (k6_tmap_1(A_2444, u1_struct_0(B_2445))=k8_tmap_1(A_2444, B_2445) | ~l1_pre_topc(k8_tmap_1(A_2444, B_2445)) | ~v1_pre_topc(k8_tmap_1(A_2444, B_2445)) | ~m1_pre_topc(B_2445, A_2444) | ~l1_pre_topc(A_2444) | ~v2_pre_topc(A_2444) | v2_struct_0(A_2444))), inference(resolution, [status(thm)], [c_46, c_49047])).
% 50.68/35.57  tff(c_209371, plain, (![A_2912, B_2913]: (k6_tmap_1(A_2912, u1_struct_0(B_2913))=k8_tmap_1(A_2912, B_2913) | ~l1_pre_topc(k8_tmap_1(A_2912, B_2913)) | ~m1_pre_topc(B_2913, A_2912) | ~l1_pre_topc(A_2912) | ~v2_pre_topc(A_2912) | v2_struct_0(A_2912))), inference(resolution, [status(thm)], [c_48, c_167570])).
% 50.68/35.57  tff(c_209675, plain, (![A_2916, B_2917]: (k6_tmap_1(A_2916, u1_struct_0(B_2917))=k8_tmap_1(A_2916, B_2917) | ~m1_pre_topc(B_2917, A_2916) | ~l1_pre_topc(A_2916) | ~v2_pre_topc(A_2916) | v2_struct_0(A_2916))), inference(resolution, [status(thm)], [c_44, c_209371])).
% 50.68/35.57  tff(c_45003, plain, (![B_940, A_941]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_940), u1_pre_topc(B_940)), A_941) | ~m1_pre_topc(B_940, A_941) | ~l1_pre_topc(A_941))), inference(cnfTransformation, [status(thm)], [f_197])).
% 50.68/35.57  tff(c_12, plain, (![B_9, A_7]: (l1_pre_topc(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 50.68/35.57  tff(c_45019, plain, (![B_942, A_943]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_942), u1_pre_topc(B_942))) | ~m1_pre_topc(B_942, A_943) | ~l1_pre_topc(A_943))), inference(resolution, [status(thm)], [c_45003, c_12])).
% 50.68/35.57  tff(c_45025, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_72, c_45019])).
% 50.68/35.57  tff(c_45030, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_45025])).
% 50.68/35.57  tff(c_44976, plain, (![B_935, A_936]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_935), u1_pre_topc(B_935))) | ~m1_pre_topc(B_935, A_936) | ~l1_pre_topc(A_936))), inference(cnfTransformation, [status(thm)], [f_197])).
% 50.68/35.57  tff(c_44980, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_72, c_44976])).
% 50.68/35.57  tff(c_44984, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_44980])).
% 50.68/35.57  tff(c_103, plain, (![B_90, A_91]: (l1_pre_topc(B_90) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 50.68/35.57  tff(c_109, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_72, c_103])).
% 50.68/35.57  tff(c_113, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_109])).
% 50.68/35.57  tff(c_14, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 50.68/35.57  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 50.68/35.57  tff(c_45063, plain, (![D_951, B_952, C_953, A_954]: (D_951=B_952 | g1_pre_topc(C_953, D_951)!=g1_pre_topc(A_954, B_952) | ~m1_subset_1(B_952, k1_zfmisc_1(k1_zfmisc_1(A_954))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 50.68/35.57  tff(c_45065, plain, (![A_3, B_952, A_954]: (u1_pre_topc(A_3)=B_952 | g1_pre_topc(A_954, B_952)!=A_3 | ~m1_subset_1(B_952, k1_zfmisc_1(k1_zfmisc_1(A_954))) | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_45063])).
% 50.68/35.57  tff(c_45432, plain, (![A_1020, B_1021]: (u1_pre_topc(g1_pre_topc(A_1020, B_1021))=B_1021 | ~m1_subset_1(B_1021, k1_zfmisc_1(k1_zfmisc_1(A_1020))) | ~v1_pre_topc(g1_pre_topc(A_1020, B_1021)) | ~l1_pre_topc(g1_pre_topc(A_1020, B_1021)))), inference(reflexivity, [status(thm), theory('equality')], [c_45065])).
% 50.68/35.57  tff(c_46627, plain, (![A_1110]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_1110), u1_pre_topc(A_1110)))=u1_pre_topc(A_1110) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_1110), u1_pre_topc(A_1110))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_1110), u1_pre_topc(A_1110))) | ~l1_pre_topc(A_1110))), inference(resolution, [status(thm)], [c_14, c_45432])).
% 50.68/35.57  tff(c_46651, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_44984, c_46627])).
% 50.68/35.57  tff(c_46663, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_45030, c_46651])).
% 50.68/35.57  tff(c_46809, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_pre_topc('#skF_4'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_46663, c_6])).
% 50.68/35.57  tff(c_46903, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_pre_topc('#skF_4'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_45030, c_44984, c_46809])).
% 50.68/35.57  tff(c_66, plain, (![A_73]: (m1_pre_topc(A_73, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_208])).
% 50.68/35.57  tff(c_44994, plain, (![B_938, A_939]: (m1_pre_topc(B_938, A_939) | ~m1_pre_topc(B_938, g1_pre_topc(u1_struct_0(A_939), u1_pre_topc(A_939))) | ~l1_pre_topc(A_939))), inference(cnfTransformation, [status(thm)], [f_81])).
% 50.68/35.57  tff(c_45002, plain, (![A_939]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_939), u1_pre_topc(A_939)), A_939) | ~l1_pre_topc(A_939) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_939), u1_pre_topc(A_939))))), inference(resolution, [status(thm)], [c_66, c_44994])).
% 50.68/35.57  tff(c_60, plain, (![B_69, A_67]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_69), u1_pre_topc(B_69)), A_67) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_197])).
% 50.68/35.57  tff(c_45041, plain, (![C_947, A_948, B_949]: (m1_pre_topc(C_947, A_948) | ~m1_pre_topc(C_947, B_949) | ~m1_pre_topc(B_949, A_948) | ~l1_pre_topc(A_948) | ~v2_pre_topc(A_948))), inference(cnfTransformation, [status(thm)], [f_227])).
% 50.68/35.57  tff(c_45633, plain, (![B_1046, A_1047, A_1048]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_1046), u1_pre_topc(B_1046)), A_1047) | ~m1_pre_topc(A_1048, A_1047) | ~l1_pre_topc(A_1047) | ~v2_pre_topc(A_1047) | ~m1_pre_topc(B_1046, A_1048) | ~l1_pre_topc(A_1048))), inference(resolution, [status(thm)], [c_60, c_45041])).
% 50.68/35.57  tff(c_45641, plain, (![B_1046]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_1046), u1_pre_topc(B_1046)), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_1046, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_45633])).
% 50.68/35.57  tff(c_45647, plain, (![B_1046]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_1046), u1_pre_topc(B_1046)), '#skF_3') | ~m1_pre_topc(B_1046, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_78, c_76, c_45641])).
% 50.68/35.57  tff(c_46755, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_pre_topc('#skF_4')), '#skF_3') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46663, c_45647])).
% 50.68/35.57  tff(c_47081, plain, (~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_46755])).
% 50.68/35.57  tff(c_47087, plain, (~l1_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_45002, c_47081])).
% 50.68/35.57  tff(c_47100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45030, c_113, c_47087])).
% 50.68/35.57  tff(c_47101, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_pre_topc('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_46755])).
% 50.68/35.57  tff(c_47658, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46903, c_47101])).
% 50.68/35.57  tff(c_46818, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_46663, c_14])).
% 50.68/35.57  tff(c_46909, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_45030, c_46818])).
% 50.68/35.57  tff(c_22, plain, (![C_16, A_12, D_17, B_13]: (C_16=A_12 | g1_pre_topc(C_16, D_17)!=g1_pre_topc(A_12, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 50.68/35.57  tff(c_47691, plain, (![C_16, D_17]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=C_16 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_16, D_17) | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))))), inference(superposition, [status(thm), theory('equality')], [c_46903, c_22])).
% 50.68/35.57  tff(c_47714, plain, (![C_16, D_17]: (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=C_16 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_16, D_17))), inference(demodulation, [status(thm), theory('equality')], [c_46909, c_47691])).
% 50.68/35.57  tff(c_48023, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_struct_0('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_47714])).
% 50.68/35.57  tff(c_68, plain, (![B_76, A_74]: (r1_tarski(u1_struct_0(B_76), u1_struct_0(A_74)) | ~m1_pre_topc(B_76, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_215])).
% 50.68/35.57  tff(c_159075, plain, (![A_2327]: (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0(A_2327)) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), A_2327) | ~l1_pre_topc(A_2327))), inference(superposition, [status(thm), theory('equality')], [c_48023, c_68])).
% 50.68/35.57  tff(c_159088, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_47658, c_159075])).
% 50.68/35.57  tff(c_159128, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_159088])).
% 50.68/35.57  tff(c_92, plain, (v1_tsep_1('#skF_4', '#skF_3') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k8_tmap_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_247])).
% 50.68/35.57  tff(c_114, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k8_tmap_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_92])).
% 50.68/35.57  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k8_tmap_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 50.68/35.57  tff(c_95, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k8_tmap_1('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_82])).
% 50.68/35.57  tff(c_156, plain, (~v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_95])).
% 50.68/35.57  tff(c_726, plain, (![A_158, B_159]: (m1_subset_1('#skF_2'(A_158, B_159), k1_zfmisc_1(u1_struct_0(A_158))) | v1_tsep_1(B_159, A_158) | ~m1_pre_topc(B_159, A_158) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_121])).
% 50.68/35.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 50.68/35.57  tff(c_741, plain, (![A_158, B_159]: (r1_tarski('#skF_2'(A_158, B_159), u1_struct_0(A_158)) | v1_tsep_1(B_159, A_158) | ~m1_pre_topc(B_159, A_158) | ~l1_pre_topc(A_158))), inference(resolution, [status(thm)], [c_726, c_2])).
% 50.68/35.57  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 50.68/35.57  tff(c_22307, plain, (![B_575, A_576]: (r2_hidden(B_575, u1_pre_topc(A_576)) | k5_tmap_1(A_576, B_575)!=u1_pre_topc(A_576) | ~m1_subset_1(B_575, k1_zfmisc_1(u1_struct_0(A_576))) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576) | v2_struct_0(A_576))), inference(cnfTransformation, [status(thm)], [f_174])).
% 50.68/35.57  tff(c_30685, plain, (![A_756, A_757]: (r2_hidden(A_756, u1_pre_topc(A_757)) | k5_tmap_1(A_757, A_756)!=u1_pre_topc(A_757) | ~l1_pre_topc(A_757) | ~v2_pre_topc(A_757) | v2_struct_0(A_757) | ~r1_tarski(A_756, u1_struct_0(A_757)))), inference(resolution, [status(thm)], [c_4, c_22307])).
% 50.68/35.57  tff(c_439, plain, (![B_138, A_139]: (u1_struct_0(B_138)='#skF_2'(A_139, B_138) | v1_tsep_1(B_138, A_139) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_121])).
% 50.68/35.57  tff(c_442, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_439, c_156])).
% 50.68/35.57  tff(c_445, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_442])).
% 50.68/35.57  tff(c_463, plain, (![A_70]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc('#skF_4', A_70) | ~l1_pre_topc(A_70))), inference(superposition, [status(thm), theory('equality')], [c_445, c_64])).
% 50.68/35.57  tff(c_196, plain, (![B_104, A_105]: (m1_pre_topc(B_104, A_105) | ~m1_pre_topc(B_104, g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_81])).
% 50.68/35.57  tff(c_202, plain, (![B_104]: (m1_pre_topc(B_104, '#skF_3') | ~m1_pre_topc(B_104, k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_196])).
% 50.68/35.57  tff(c_210, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_3') | ~m1_pre_topc(B_106, k8_tmap_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_202])).
% 50.68/35.57  tff(c_215, plain, (m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_210])).
% 50.68/35.57  tff(c_216, plain, (~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_215])).
% 50.68/35.57  tff(c_217, plain, (![B_107, A_108]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_107), u1_pre_topc(B_107)), A_108) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_197])).
% 50.68/35.57  tff(c_241, plain, (![A_109]: (m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), A_109) | ~m1_pre_topc('#skF_3', A_109) | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_114, c_217])).
% 50.68/35.57  tff(c_254, plain, (![A_109]: (l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_241, c_12])).
% 50.68/35.57  tff(c_261, plain, (![A_110]: (~m1_pre_topc('#skF_3', A_110) | ~l1_pre_topc(A_110))), inference(negUnitSimplification, [status(thm)], [c_216, c_254])).
% 50.68/35.57  tff(c_265, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_261])).
% 50.68/35.57  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_265])).
% 50.68/35.57  tff(c_271, plain, (l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_215])).
% 50.68/35.57  tff(c_144, plain, (![A_95]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_95), u1_pre_topc(A_95))) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_65])).
% 50.68/35.57  tff(c_150, plain, (v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114, c_144])).
% 50.68/35.57  tff(c_152, plain, (v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_150])).
% 50.68/35.57  tff(c_153, plain, (v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_152])).
% 50.68/35.57  tff(c_413, plain, (![C_122, A_123, D_124, B_125]: (C_122=A_123 | g1_pre_topc(C_122, D_124)!=g1_pre_topc(A_123, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(k1_zfmisc_1(A_123))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 50.68/35.57  tff(c_421, plain, (![C_122, D_124]: (u1_struct_0('#skF_3')=C_122 | k8_tmap_1('#skF_3', '#skF_4')!=g1_pre_topc(C_122, D_124) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_114, c_413])).
% 50.68/35.57  tff(c_21597, plain, (~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_421])).
% 50.68/35.57  tff(c_21600, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_21597])).
% 50.68/35.57  tff(c_21607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_21600])).
% 50.68/35.57  tff(c_21628, plain, (![C_552, D_553]: (u1_struct_0('#skF_3')=C_552 | k8_tmap_1('#skF_3', '#skF_4')!=g1_pre_topc(C_552, D_553))), inference(splitRight, [status(thm)], [c_421])).
% 50.68/35.57  tff(c_21638, plain, (![A_554]: (u1_struct_0(A_554)=u1_struct_0('#skF_3') | k8_tmap_1('#skF_3', '#skF_4')!=A_554 | ~v1_pre_topc(A_554) | ~l1_pre_topc(A_554))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21628])).
% 50.68/35.57  tff(c_21653, plain, (u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_153, c_21638])).
% 50.68/35.57  tff(c_21664, plain, (u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_21653])).
% 50.68/35.57  tff(c_21742, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')))=k8_tmap_1('#skF_3', '#skF_4') | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_6])).
% 50.68/35.57  tff(c_21779, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')))=k8_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_153, c_21742])).
% 50.68/35.57  tff(c_21609, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_421])).
% 50.68/35.57  tff(c_427, plain, (![D_128, B_129, C_130, A_131]: (D_128=B_129 | g1_pre_topc(C_130, D_128)!=g1_pre_topc(A_131, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(k1_zfmisc_1(A_131))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 50.68/35.57  tff(c_435, plain, (![D_128, C_130]: (u1_pre_topc('#skF_3')=D_128 | k8_tmap_1('#skF_3', '#skF_4')!=g1_pre_topc(C_130, D_128) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_114, c_427])).
% 50.68/35.57  tff(c_21868, plain, (![D_560, C_561]: (u1_pre_topc('#skF_3')=D_560 | k8_tmap_1('#skF_3', '#skF_4')!=g1_pre_topc(C_561, D_560))), inference(demodulation, [status(thm), theory('equality')], [c_21609, c_435])).
% 50.68/35.57  tff(c_21878, plain, (u1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))=u1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21779, c_21868])).
% 50.68/35.57  tff(c_8, plain, (![B_6, A_4]: (v3_pre_topc(B_6, A_4) | ~r2_hidden(B_6, u1_pre_topc(A_4)) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.68/35.57  tff(c_21712, plain, (![B_6]: (v3_pre_topc(B_6, k8_tmap_1('#skF_3', '#skF_4')) | ~r2_hidden(B_6, u1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_8])).
% 50.68/35.57  tff(c_21764, plain, (![B_6]: (v3_pre_topc(B_6, k8_tmap_1('#skF_3', '#skF_4')) | ~r2_hidden(B_6, u1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_21712])).
% 50.68/35.57  tff(c_27215, plain, (![B_708]: (v3_pre_topc(B_708, k8_tmap_1('#skF_3', '#skF_4')) | ~r2_hidden(B_708, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_708, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_21878, c_21764])).
% 50.68/35.57  tff(c_27237, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_463, c_27215])).
% 50.68/35.57  tff(c_27262, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_27237])).
% 50.68/35.57  tff(c_27272, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(splitLeft, [status(thm)], [c_27262])).
% 50.68/35.57  tff(c_30692, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30685, c_27272])).
% 50.68/35.57  tff(c_30736, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_30692])).
% 50.68/35.57  tff(c_30737, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=u1_pre_topc('#skF_3') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_30736])).
% 50.68/35.57  tff(c_30761, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_30737])).
% 50.68/35.57  tff(c_30764, plain, (v1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_741, c_30761])).
% 50.68/35.57  tff(c_30770, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_30764])).
% 50.68/35.57  tff(c_30772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_30770])).
% 50.68/35.57  tff(c_30773, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_30737])).
% 50.68/35.57  tff(c_30774, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_30737])).
% 50.68/35.57  tff(c_21794, plain, (![A_557, B_558]: (u1_struct_0(k6_tmap_1(A_557, B_558))=u1_struct_0(A_557) | ~m1_subset_1(B_558, k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557) | v2_struct_0(A_557))), inference(cnfTransformation, [status(thm)], [f_188])).
% 50.68/35.57  tff(c_21823, plain, (![A_557, A_1]: (u1_struct_0(k6_tmap_1(A_557, A_1))=u1_struct_0(A_557) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557) | v2_struct_0(A_557) | ~r1_tarski(A_1, u1_struct_0(A_557)))), inference(resolution, [status(thm)], [c_4, c_21794])).
% 50.68/35.57  tff(c_30780, plain, (u1_struct_0(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30774, c_21823])).
% 50.68/35.57  tff(c_30787, plain, (u1_struct_0(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=u1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_30780])).
% 50.68/35.57  tff(c_30788, plain, (u1_struct_0(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_30787])).
% 50.68/35.57  tff(c_21949, plain, (![A_562, B_563]: (u1_pre_topc(k6_tmap_1(A_562, B_563))=k5_tmap_1(A_562, B_563) | ~m1_subset_1(B_563, k1_zfmisc_1(u1_struct_0(A_562))) | ~l1_pre_topc(A_562) | ~v2_pre_topc(A_562) | v2_struct_0(A_562))), inference(cnfTransformation, [status(thm)], [f_188])).
% 50.68/35.57  tff(c_21978, plain, (![A_562, A_1]: (u1_pre_topc(k6_tmap_1(A_562, A_1))=k5_tmap_1(A_562, A_1) | ~l1_pre_topc(A_562) | ~v2_pre_topc(A_562) | v2_struct_0(A_562) | ~r1_tarski(A_1, u1_struct_0(A_562)))), inference(resolution, [status(thm)], [c_4, c_21949])).
% 50.68/35.57  tff(c_30777, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30774, c_21978])).
% 50.68/35.57  tff(c_30783, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_30777])).
% 50.68/35.57  tff(c_30784, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_30783])).
% 50.68/35.57  tff(c_168, plain, (![B_99, A_100]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_99), u1_pre_topc(B_99))) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_197])).
% 50.68/35.57  tff(c_173, plain, (![A_73]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_73), u1_pre_topc(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_66, c_168])).
% 50.68/35.57  tff(c_31159, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))), k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_30784, c_173])).
% 50.68/35.57  tff(c_31189, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30788, c_31159])).
% 50.68/35.57  tff(c_32958, plain, (~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_31189])).
% 50.68/35.57  tff(c_270, plain, (m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_215])).
% 50.68/35.57  tff(c_158, plain, (![A_98]: (~v2_struct_0(g1_pre_topc(u1_struct_0(A_98), u1_pre_topc(A_98))) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 50.68/35.57  tff(c_164, plain, (~v2_struct_0(k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114, c_158])).
% 50.68/35.57  tff(c_166, plain, (~v2_struct_0(k8_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_164])).
% 50.68/35.57  tff(c_167, plain, (~v2_struct_0(k8_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_166])).
% 50.68/35.57  tff(c_26333, plain, (![A_688, A_689]: (u1_struct_0(k6_tmap_1(A_688, A_689))=u1_struct_0(A_688) | ~l1_pre_topc(A_688) | ~v2_pre_topc(A_688) | v2_struct_0(A_688) | ~r1_tarski(A_689, u1_struct_0(A_688)))), inference(resolution, [status(thm)], [c_4, c_21794])).
% 50.68/35.57  tff(c_26351, plain, (![A_689]: (u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_3', '#skF_4'), A_689))=u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | v2_struct_0(k8_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(A_689, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_26333])).
% 50.68/35.57  tff(c_26372, plain, (![A_689]: (u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_3', '#skF_4'), A_689))=u1_struct_0('#skF_3') | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | v2_struct_0(k8_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(A_689, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_21664, c_26351])).
% 50.68/35.57  tff(c_26373, plain, (![A_689]: (u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_3', '#skF_4'), A_689))=u1_struct_0('#skF_3') | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~r1_tarski(A_689, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_167, c_26372])).
% 50.68/35.57  tff(c_26805, plain, (~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_26373])).
% 50.68/35.57  tff(c_26808, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_26805])).
% 50.68/35.57  tff(c_26811, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_26808])).
% 50.68/35.57  tff(c_26813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_26811])).
% 50.68/35.57  tff(c_26815, plain, (v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_26373])).
% 50.68/35.57  tff(c_26161, plain, (![A_680, B_681]: (k6_tmap_1(A_680, u1_struct_0(B_681))=k8_tmap_1(A_680, B_681) | ~m1_subset_1(u1_struct_0(B_681), k1_zfmisc_1(u1_struct_0(A_680))) | ~l1_pre_topc(k8_tmap_1(A_680, B_681)) | ~v2_pre_topc(k8_tmap_1(A_680, B_681)) | ~v1_pre_topc(k8_tmap_1(A_680, B_681)) | ~m1_pre_topc(B_681, A_680) | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.68/35.57  tff(c_38367, plain, (![A_852, B_853]: (k6_tmap_1(A_852, u1_struct_0(B_853))=k8_tmap_1(A_852, B_853) | ~l1_pre_topc(k8_tmap_1(A_852, B_853)) | ~v2_pre_topc(k8_tmap_1(A_852, B_853)) | ~v1_pre_topc(k8_tmap_1(A_852, B_853)) | ~v2_pre_topc(A_852) | v2_struct_0(A_852) | ~m1_pre_topc(B_853, A_852) | ~l1_pre_topc(A_852))), inference(resolution, [status(thm)], [c_64, c_26161])).
% 50.68/35.57  tff(c_38370, plain, (k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k8_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26815, c_38367])).
% 50.68/35.57  tff(c_38376, plain, (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=k8_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_78, c_153, c_271, c_445, c_38370])).
% 50.68/35.57  tff(c_38377, plain, (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=k8_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_38376])).
% 50.68/35.57  tff(c_22154, plain, (![A_568]: (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_568)) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), A_568) | ~l1_pre_topc(A_568))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_68])).
% 50.68/35.57  tff(c_22160, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_22154])).
% 50.68/35.57  tff(c_22165, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_22160])).
% 50.68/35.57  tff(c_22217, plain, (~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_22165])).
% 50.68/35.57  tff(c_22246, plain, (~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_22217])).
% 50.68/35.57  tff(c_22253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_22246])).
% 50.68/35.57  tff(c_22255, plain, (m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_22165])).
% 50.68/35.57  tff(c_22168, plain, (![B_569, A_570]: (v3_pre_topc(u1_struct_0(B_569), A_570) | ~m1_subset_1(u1_struct_0(B_569), k1_zfmisc_1(u1_struct_0(A_570))) | ~v1_tsep_1(B_569, A_570) | ~m1_pre_topc(B_569, A_570) | ~l1_pre_topc(A_570))), inference(cnfTransformation, [status(thm)], [f_121])).
% 50.68/35.57  tff(c_22205, plain, (![B_72, A_70]: (v3_pre_topc(u1_struct_0(B_72), A_70) | ~v1_tsep_1(B_72, A_70) | ~m1_pre_topc(B_72, A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_64, c_22168])).
% 50.68/35.57  tff(c_22254, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_22165])).
% 50.68/35.57  tff(c_585, plain, (![B_146, A_147]: (r2_hidden(B_146, u1_pre_topc(A_147)) | ~v3_pre_topc(B_146, A_147) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.68/35.57  tff(c_599, plain, (![A_1, A_147]: (r2_hidden(A_1, u1_pre_topc(A_147)) | ~v3_pre_topc(A_1, A_147) | ~l1_pre_topc(A_147) | ~r1_tarski(A_1, u1_struct_0(A_147)))), inference(resolution, [status(thm)], [c_4, c_585])).
% 50.68/35.57  tff(c_21730, plain, (![B_72]: (m1_subset_1(u1_struct_0(B_72), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_72, k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_64])).
% 50.68/35.57  tff(c_21772, plain, (![B_72]: (m1_subset_1(u1_struct_0(B_72), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_72, k8_tmap_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_21730])).
% 50.68/35.57  tff(c_22493, plain, (![A_581, B_582]: (k5_tmap_1(A_581, B_582)=u1_pre_topc(A_581) | ~r2_hidden(B_582, u1_pre_topc(A_581)) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_581))) | ~l1_pre_topc(A_581) | ~v2_pre_topc(A_581) | v2_struct_0(A_581))), inference(cnfTransformation, [status(thm)], [f_174])).
% 50.68/35.57  tff(c_22499, plain, (![B_72]: (k5_tmap_1('#skF_3', u1_struct_0(B_72))=u1_pre_topc('#skF_3') | ~r2_hidden(u1_struct_0(B_72), u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_72, k8_tmap_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_21772, c_22493])).
% 50.68/35.57  tff(c_22521, plain, (![B_72]: (k5_tmap_1('#skF_3', u1_struct_0(B_72))=u1_pre_topc('#skF_3') | ~r2_hidden(u1_struct_0(B_72), u1_pre_topc('#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_72, k8_tmap_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_22499])).
% 50.68/35.57  tff(c_22549, plain, (![B_584]: (k5_tmap_1('#skF_3', u1_struct_0(B_584))=u1_pre_topc('#skF_3') | ~r2_hidden(u1_struct_0(B_584), u1_pre_topc('#skF_3')) | ~m1_pre_topc(B_584, k8_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_22521])).
% 50.68/35.57  tff(c_22555, plain, (k5_tmap_1('#skF_3', u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')))=u1_pre_topc('#skF_3') | ~r2_hidden(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_22549])).
% 50.68/35.57  tff(c_22563, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_3'))=u1_pre_topc('#skF_3') | ~r2_hidden(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22255, c_21664, c_22555])).
% 50.68/35.57  tff(c_22568, plain, (~r2_hidden(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(splitLeft, [status(thm)], [c_22563])).
% 50.68/35.57  tff(c_22571, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_599, c_22568])).
% 50.68/35.57  tff(c_22574, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22254, c_76, c_22571])).
% 50.68/35.57  tff(c_22577, plain, (~v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22205, c_22574])).
% 50.68/35.57  tff(c_22580, plain, (~v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22577])).
% 50.68/35.57  tff(c_22581, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_22580])).
% 50.68/35.57  tff(c_22584, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_22581])).
% 50.68/35.57  tff(c_22588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_22584])).
% 50.68/35.57  tff(c_22590, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_22580])).
% 50.68/35.57  tff(c_38, plain, (![B_49, A_43]: (u1_struct_0(B_49)='#skF_2'(A_43, B_49) | v1_tsep_1(B_49, A_43) | ~m1_pre_topc(B_49, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_121])).
% 50.68/35.57  tff(c_22589, plain, (~v1_tsep_1('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_22580])).
% 50.68/35.57  tff(c_22650, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_22589])).
% 50.68/35.57  tff(c_22653, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22590, c_22650])).
% 50.68/35.57  tff(c_22712, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22653, c_463])).
% 50.68/35.57  tff(c_22793, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_22712])).
% 50.68/35.57  tff(c_10, plain, (![B_6, A_4]: (r2_hidden(B_6, u1_pre_topc(A_4)) | ~v3_pre_topc(B_6, A_4) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.68/35.57  tff(c_22718, plain, (![B_6]: (r2_hidden(B_6, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_6, '#skF_3') | ~m1_subset_1(B_6, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22653, c_10])).
% 50.68/35.57  tff(c_24714, plain, (![B_632]: (r2_hidden(B_632, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_632, '#skF_3') | ~m1_subset_1(B_632, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22718])).
% 50.68/35.57  tff(c_24735, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_22793, c_24714])).
% 50.68/35.57  tff(c_24737, plain, (~v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_24735])).
% 50.68/35.57  tff(c_22727, plain, (![B_6]: (v3_pre_topc(B_6, '#skF_3') | ~r2_hidden(B_6, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_6, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22653, c_8])).
% 50.68/35.57  tff(c_24926, plain, (![B_637]: (v3_pre_topc(B_637, '#skF_3') | ~r2_hidden(B_637, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_637, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_22727])).
% 50.68/35.57  tff(c_24938, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_22793, c_24926])).
% 50.68/35.57  tff(c_24949, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_24737, c_24938])).
% 50.68/35.57  tff(c_52, plain, (![B_63, A_61]: (r2_hidden(B_63, u1_pre_topc(A_61)) | k5_tmap_1(A_61, B_63)!=u1_pre_topc(A_61) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_174])).
% 50.68/35.57  tff(c_22686, plain, (![B_63]: (r2_hidden(B_63, u1_pre_topc('#skF_3')) | k5_tmap_1('#skF_3', B_63)!=u1_pre_topc('#skF_3') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22653, c_52])).
% 50.68/35.57  tff(c_22776, plain, (![B_63]: (r2_hidden(B_63, u1_pre_topc('#skF_3')) | k5_tmap_1('#skF_3', B_63)!=u1_pre_topc('#skF_3') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_22686])).
% 50.68/35.57  tff(c_23534, plain, (![B_607]: (r2_hidden(B_607, u1_pre_topc('#skF_3')) | k5_tmap_1('#skF_3', B_607)!=u1_pre_topc('#skF_3') | ~m1_subset_1(B_607, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_22776])).
% 50.68/35.57  tff(c_23552, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3')) | k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=u1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22793, c_23534])).
% 50.68/35.57  tff(c_25121, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=u1_pre_topc('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_24949, c_23552])).
% 50.68/35.57  tff(c_23314, plain, (![A_603, B_604]: (k6_tmap_1(A_603, u1_struct_0(B_604))=k8_tmap_1(A_603, B_604) | ~m1_subset_1(u1_struct_0(B_604), k1_zfmisc_1(u1_struct_0(A_603))) | ~l1_pre_topc(k8_tmap_1(A_603, B_604)) | ~v2_pre_topc(k8_tmap_1(A_603, B_604)) | ~v1_pre_topc(k8_tmap_1(A_603, B_604)) | ~m1_pre_topc(B_604, A_603) | ~l1_pre_topc(A_603) | ~v2_pre_topc(A_603) | v2_struct_0(A_603))), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.68/35.57  tff(c_23332, plain, (![B_604]: (k6_tmap_1('#skF_3', u1_struct_0(B_604))=k8_tmap_1('#skF_3', B_604) | ~m1_subset_1(u1_struct_0(B_604), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc(k8_tmap_1('#skF_3', B_604)) | ~v2_pre_topc(k8_tmap_1('#skF_3', B_604)) | ~v1_pre_topc(k8_tmap_1('#skF_3', B_604)) | ~m1_pre_topc(B_604, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22653, c_23314])).
% 50.68/35.57  tff(c_23352, plain, (![B_604]: (k6_tmap_1('#skF_3', u1_struct_0(B_604))=k8_tmap_1('#skF_3', B_604) | ~m1_subset_1(u1_struct_0(B_604), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc(k8_tmap_1('#skF_3', B_604)) | ~v2_pre_topc(k8_tmap_1('#skF_3', B_604)) | ~v1_pre_topc(k8_tmap_1('#skF_3', B_604)) | ~m1_pre_topc(B_604, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_23332])).
% 50.68/35.57  tff(c_25351, plain, (![B_648]: (k6_tmap_1('#skF_3', u1_struct_0(B_648))=k8_tmap_1('#skF_3', B_648) | ~m1_subset_1(u1_struct_0(B_648), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc(k8_tmap_1('#skF_3', B_648)) | ~v2_pre_topc(k8_tmap_1('#skF_3', B_648)) | ~v1_pre_topc(k8_tmap_1('#skF_3', B_648)) | ~m1_pre_topc(B_648, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_23352])).
% 50.68/35.57  tff(c_25381, plain, (k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k8_tmap_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_445, c_25351])).
% 50.68/35.57  tff(c_25400, plain, (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=k8_tmap_1('#skF_3', '#skF_4') | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_153, c_271, c_22793, c_445, c_25381])).
% 50.68/35.57  tff(c_25402, plain, (~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_25400])).
% 50.68/35.57  tff(c_25405, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_25402])).
% 50.68/35.57  tff(c_25408, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_25405])).
% 50.68/35.57  tff(c_25410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_25408])).
% 50.68/35.57  tff(c_25411, plain, (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=k8_tmap_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_25400])).
% 50.68/35.57  tff(c_56, plain, (![A_64, B_66]: (u1_pre_topc(k6_tmap_1(A_64, B_66))=k5_tmap_1(A_64, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_188])).
% 50.68/35.57  tff(c_22698, plain, (![B_66]: (u1_pre_topc(k6_tmap_1('#skF_3', B_66))=k5_tmap_1('#skF_3', B_66) | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22653, c_56])).
% 50.68/35.57  tff(c_22781, plain, (![B_66]: (u1_pre_topc(k6_tmap_1('#skF_3', B_66))=k5_tmap_1('#skF_3', B_66) | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_22698])).
% 50.68/35.57  tff(c_23020, plain, (![B_594]: (u1_pre_topc(k6_tmap_1('#skF_3', B_594))=k5_tmap_1('#skF_3', B_594) | ~m1_subset_1(B_594, k1_zfmisc_1('#skF_2'('#skF_3', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_22781])).
% 50.68/35.57  tff(c_23028, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_22793, c_23020])).
% 50.68/35.57  tff(c_25418, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=u1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_25411, c_23028])).
% 50.68/35.57  tff(c_25420, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21878, c_25418])).
% 50.68/35.57  tff(c_25422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25121, c_25420])).
% 50.68/35.57  tff(c_25424, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_24735])).
% 50.68/35.57  tff(c_36, plain, (![A_43, B_49]: (~v3_pre_topc('#skF_2'(A_43, B_49), A_43) | v1_tsep_1(B_49, A_43) | ~m1_pre_topc(B_49, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_121])).
% 50.68/35.57  tff(c_25427, plain, (v1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_25424, c_36])).
% 50.68/35.57  tff(c_25430, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_25427])).
% 50.68/35.57  tff(c_25432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_25430])).
% 50.68/35.57  tff(c_25433, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_3'))=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_22563])).
% 50.68/35.57  tff(c_25435, plain, (![A_649, B_650]: (g1_pre_topc(u1_struct_0(A_649), k5_tmap_1(A_649, B_650))=k6_tmap_1(A_649, B_650) | ~m1_subset_1(B_650, k1_zfmisc_1(u1_struct_0(A_649))) | ~l1_pre_topc(A_649) | ~v2_pre_topc(A_649) | v2_struct_0(A_649))), inference(cnfTransformation, [status(thm)], [f_133])).
% 50.68/35.57  tff(c_25439, plain, (![B_72]: (g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', u1_struct_0(B_72)))=k6_tmap_1('#skF_3', u1_struct_0(B_72)) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_72, k8_tmap_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_21772, c_25435])).
% 50.68/35.57  tff(c_25455, plain, (![B_72]: (g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', u1_struct_0(B_72)))=k6_tmap_1('#skF_3', u1_struct_0(B_72)) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_72, k8_tmap_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_25439])).
% 50.68/35.57  tff(c_25488, plain, (![B_651]: (g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', u1_struct_0(B_651)))=k6_tmap_1('#skF_3', u1_struct_0(B_651)) | ~m1_pre_topc(B_651, k8_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_25455])).
% 50.68/35.57  tff(c_25517, plain, (g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', u1_struct_0('#skF_3')))=k6_tmap_1('#skF_3', u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_25488])).
% 50.68/35.57  tff(c_25527, plain, (k6_tmap_1('#skF_3', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22255, c_114, c_25433, c_21664, c_25517])).
% 50.68/35.57  tff(c_25596, plain, (![A_655]: (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_655))) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), A_655) | ~l1_pre_topc(A_655))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_64])).
% 50.68/35.57  tff(c_25627, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), k8_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_25596])).
% 50.68/35.57  tff(c_25641, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_22255, c_25627])).
% 50.68/35.57  tff(c_26164, plain, (k6_tmap_1('#skF_3', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_3', '#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_25641, c_26161])).
% 50.68/35.57  tff(c_26197, plain, (k8_tmap_1('#skF_3', '#skF_3')=k8_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_25527, c_26164])).
% 50.68/35.57  tff(c_26198, plain, (k8_tmap_1('#skF_3', '#skF_3')=k8_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_26197])).
% 50.68/35.57  tff(c_26245, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_26198])).
% 50.68/35.57  tff(c_26248, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_26245])).
% 50.68/35.57  tff(c_26252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_26248])).
% 50.68/35.57  tff(c_26254, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_26198])).
% 50.68/35.57  tff(c_370, plain, (![C_117, A_118, B_119]: (m1_pre_topc(C_117, A_118) | ~m1_pre_topc(C_117, B_119) | ~m1_pre_topc(B_119, A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_227])).
% 50.68/35.57  tff(c_31598, plain, (![B_765, A_766, A_767]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_765), u1_pre_topc(B_765)), A_766) | ~m1_pre_topc(A_767, A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | ~m1_pre_topc(B_765, A_767) | ~l1_pre_topc(A_767))), inference(resolution, [status(thm)], [c_60, c_370])).
% 50.68/35.57  tff(c_31602, plain, (![B_765]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_765), u1_pre_topc(B_765)), '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_765, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_26254, c_31598])).
% 50.68/35.57  tff(c_31998, plain, (![B_772]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_772), u1_pre_topc(B_772)), '#skF_3') | ~m1_pre_topc(B_772, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_31602])).
% 50.68/35.57  tff(c_32013, plain, (![B_772]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_772), u1_pre_topc(B_772))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_772, '#skF_3'))), inference(resolution, [status(thm)], [c_31998, c_12])).
% 50.68/35.57  tff(c_32100, plain, (![B_773]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_773), u1_pre_topc(B_773))) | ~m1_pre_topc(B_773, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_32013])).
% 50.68/35.57  tff(c_32103, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))), k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))) | ~m1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30784, c_32100])).
% 50.68/35.57  tff(c_32158, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))) | ~m1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30788, c_32103])).
% 50.68/35.57  tff(c_33275, plain, (~m1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_32158])).
% 50.68/35.57  tff(c_38379, plain, (~m1_pre_topc(k8_tmap_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38377, c_33275])).
% 50.68/35.57  tff(c_38388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_38379])).
% 50.68/35.57  tff(c_38390, plain, (m1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_32158])).
% 50.68/35.57  tff(c_38405, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38390, c_12])).
% 50.68/35.57  tff(c_38424, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_38405])).
% 50.68/35.57  tff(c_38426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32958, c_38424])).
% 50.68/35.57  tff(c_38428, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_31189])).
% 50.68/35.57  tff(c_25466, plain, (![A_649, A_1]: (g1_pre_topc(u1_struct_0(A_649), k5_tmap_1(A_649, A_1))=k6_tmap_1(A_649, A_1) | ~l1_pre_topc(A_649) | ~v2_pre_topc(A_649) | v2_struct_0(A_649) | ~r1_tarski(A_1, u1_struct_0(A_649)))), inference(resolution, [status(thm)], [c_4, c_25435])).
% 50.68/35.57  tff(c_38427, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))))), inference(splitRight, [status(thm)], [c_31189])).
% 50.68/35.57  tff(c_38439, plain, (v1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25466, c_38427])).
% 50.68/35.57  tff(c_38443, plain, (v1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30774, c_78, c_76, c_38439])).
% 50.68/35.57  tff(c_38444, plain, (v1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_38443])).
% 50.68/35.57  tff(c_21874, plain, (![A_3]: (u1_pre_topc(A_3)=u1_pre_topc('#skF_3') | k8_tmap_1('#skF_3', '#skF_4')!=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21868])).
% 50.68/35.57  tff(c_38447, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))=u1_pre_topc('#skF_3') | k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=k8_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_38444, c_21874])).
% 50.68/35.57  tff(c_38453, plain, (k5_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=u1_pre_topc('#skF_3') | k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=k8_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38428, c_30784, c_38447])).
% 50.68/35.57  tff(c_38454, plain, (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))!=k8_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30773, c_38453])).
% 50.68/35.57  tff(c_44903, plain, (![A_924, B_925]: (k6_tmap_1(A_924, u1_struct_0(B_925))=k8_tmap_1(A_924, B_925) | ~l1_pre_topc(k8_tmap_1(A_924, B_925)) | ~v2_pre_topc(k8_tmap_1(A_924, B_925)) | ~v1_pre_topc(k8_tmap_1(A_924, B_925)) | ~v2_pre_topc(A_924) | v2_struct_0(A_924) | ~m1_pre_topc(B_925, A_924) | ~l1_pre_topc(A_924))), inference(resolution, [status(thm)], [c_64, c_26161])).
% 50.68/35.57  tff(c_44906, plain, (k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k8_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v1_pre_topc(k8_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26815, c_44903])).
% 50.68/35.57  tff(c_44912, plain, (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4'))=k8_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_78, c_153, c_271, c_445, c_44906])).
% 50.68/35.57  tff(c_44914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_38454, c_44912])).
% 50.68/35.57  tff(c_44916, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_27262])).
% 50.68/35.57  tff(c_514, plain, (![B_140, A_141]: (v3_pre_topc(B_140, A_141) | ~r2_hidden(B_140, u1_pre_topc(A_141)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.68/35.57  tff(c_25799, plain, (![B_661, A_662]: (v3_pre_topc(u1_struct_0(B_661), A_662) | ~r2_hidden(u1_struct_0(B_661), u1_pre_topc(A_662)) | ~m1_pre_topc(B_661, A_662) | ~l1_pre_topc(A_662))), inference(resolution, [status(thm)], [c_64, c_514])).
% 50.68/35.57  tff(c_25834, plain, (![A_662]: (v3_pre_topc(u1_struct_0('#skF_4'), A_662) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc(A_662)) | ~m1_pre_topc('#skF_4', A_662) | ~l1_pre_topc(A_662))), inference(superposition, [status(thm), theory('equality')], [c_445, c_25799])).
% 50.68/35.57  tff(c_25852, plain, (![A_662]: (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), A_662) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc(A_662)) | ~m1_pre_topc('#skF_4', A_662) | ~l1_pre_topc(A_662))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_25834])).
% 50.68/35.57  tff(c_44919, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44916, c_25852])).
% 50.68/35.57  tff(c_44925, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_44919])).
% 50.68/35.57  tff(c_44931, plain, (v1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44925, c_36])).
% 50.68/35.57  tff(c_44934, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_44931])).
% 50.68/35.57  tff(c_44936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_44934])).
% 50.68/35.57  tff(c_44937, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 50.68/35.57  tff(c_45298, plain, (![B_1002, A_1003]: (v3_pre_topc(u1_struct_0(B_1002), A_1003) | ~m1_subset_1(u1_struct_0(B_1002), k1_zfmisc_1(u1_struct_0(A_1003))) | ~v1_tsep_1(B_1002, A_1003) | ~m1_pre_topc(B_1002, A_1003) | ~l1_pre_topc(A_1003))), inference(cnfTransformation, [status(thm)], [f_121])).
% 50.68/35.57  tff(c_45311, plain, (![B_72, A_70]: (v3_pre_topc(u1_struct_0(B_72), A_70) | ~v1_tsep_1(B_72, A_70) | ~m1_pre_topc(B_72, A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_64, c_45298])).
% 50.68/35.57  tff(c_45081, plain, (![B_967, A_968]: (r2_hidden(B_967, u1_pre_topc(A_968)) | ~v3_pre_topc(B_967, A_968) | ~m1_subset_1(B_967, k1_zfmisc_1(u1_struct_0(A_968))) | ~l1_pre_topc(A_968))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.68/35.57  tff(c_45090, plain, (![A_1, A_968]: (r2_hidden(A_1, u1_pre_topc(A_968)) | ~v3_pre_topc(A_1, A_968) | ~l1_pre_topc(A_968) | ~r1_tarski(A_1, u1_struct_0(A_968)))), inference(resolution, [status(thm)], [c_4, c_45081])).
% 50.68/35.57  tff(c_45475, plain, (![A_1030, B_1031]: (k5_tmap_1(A_1030, B_1031)=u1_pre_topc(A_1030) | ~r2_hidden(B_1031, u1_pre_topc(A_1030)) | ~m1_subset_1(B_1031, k1_zfmisc_1(u1_struct_0(A_1030))) | ~l1_pre_topc(A_1030) | ~v2_pre_topc(A_1030) | v2_struct_0(A_1030))), inference(cnfTransformation, [status(thm)], [f_174])).
% 50.68/35.57  tff(c_45988, plain, (![A_1072, A_1073]: (k5_tmap_1(A_1072, A_1073)=u1_pre_topc(A_1072) | ~r2_hidden(A_1073, u1_pre_topc(A_1072)) | ~l1_pre_topc(A_1072) | ~v2_pre_topc(A_1072) | v2_struct_0(A_1072) | ~r1_tarski(A_1073, u1_struct_0(A_1072)))), inference(resolution, [status(thm)], [c_4, c_45475])).
% 50.68/35.57  tff(c_46003, plain, (![A_968, A_1]: (k5_tmap_1(A_968, A_1)=u1_pre_topc(A_968) | ~v2_pre_topc(A_968) | v2_struct_0(A_968) | ~v3_pre_topc(A_1, A_968) | ~l1_pre_topc(A_968) | ~r1_tarski(A_1, u1_struct_0(A_968)))), inference(resolution, [status(thm)], [c_45090, c_45988])).
% 50.68/35.57  tff(c_159150, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))=u1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_159128, c_46003])).
% 50.68/35.57  tff(c_159162, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_159150])).
% 50.68/35.57  tff(c_159163, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))=u1_pre_topc('#skF_3') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_159162])).
% 50.68/35.57  tff(c_159683, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_159163])).
% 50.68/35.57  tff(c_159689, plain, (~v1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_45311, c_159683])).
% 50.68/35.57  tff(c_159697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_44937, c_159689])).
% 50.68/35.57  tff(c_159698, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_159163])).
% 50.68/35.57  tff(c_45334, plain, (![B_1008, A_1009]: (r2_hidden(B_1008, u1_pre_topc(A_1009)) | k5_tmap_1(A_1009, B_1008)!=u1_pre_topc(A_1009) | ~m1_subset_1(B_1008, k1_zfmisc_1(u1_struct_0(A_1009))) | ~l1_pre_topc(A_1009) | ~v2_pre_topc(A_1009) | v2_struct_0(A_1009))), inference(cnfTransformation, [status(thm)], [f_174])).
% 50.68/35.57  tff(c_45520, plain, (![A_1034, A_1035]: (r2_hidden(A_1034, u1_pre_topc(A_1035)) | k5_tmap_1(A_1035, A_1034)!=u1_pre_topc(A_1035) | ~l1_pre_topc(A_1035) | ~v2_pre_topc(A_1035) | v2_struct_0(A_1035) | ~r1_tarski(A_1034, u1_struct_0(A_1035)))), inference(resolution, [status(thm)], [c_4, c_45334])).
% 50.68/35.57  tff(c_45091, plain, (![B_969, A_970]: (v3_pre_topc(B_969, A_970) | ~r2_hidden(B_969, u1_pre_topc(A_970)) | ~m1_subset_1(B_969, k1_zfmisc_1(u1_struct_0(A_970))) | ~l1_pre_topc(A_970))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.68/35.57  tff(c_45100, plain, (![A_1, A_970]: (v3_pre_topc(A_1, A_970) | ~r2_hidden(A_1, u1_pre_topc(A_970)) | ~l1_pre_topc(A_970) | ~r1_tarski(A_1, u1_struct_0(A_970)))), inference(resolution, [status(thm)], [c_4, c_45091])).
% 50.68/35.57  tff(c_45532, plain, (![A_1034, A_1035]: (v3_pre_topc(A_1034, A_1035) | k5_tmap_1(A_1035, A_1034)!=u1_pre_topc(A_1035) | ~l1_pre_topc(A_1035) | ~v2_pre_topc(A_1035) | v2_struct_0(A_1035) | ~r1_tarski(A_1034, u1_struct_0(A_1035)))), inference(resolution, [status(thm)], [c_45520, c_45100])).
% 50.68/35.57  tff(c_159153, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3') | k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))!=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_159128, c_45532])).
% 50.68/35.57  tff(c_159166, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3') | k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))!=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_159153])).
% 50.68/35.57  tff(c_159167, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_3') | k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))!=u1_pre_topc('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_159166])).
% 50.68/35.57  tff(c_159682, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))!=u1_pre_topc('#skF_3')), inference(splitLeft, [status(thm)], [c_159167])).
% 50.68/35.57  tff(c_159804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159698, c_159682])).
% 50.68/35.57  tff(c_159806, plain, (k5_tmap_1('#skF_3', u1_struct_0('#skF_4'))=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_159167])).
% 50.68/35.57  tff(c_45442, plain, (![A_1022, B_1023]: (g1_pre_topc(u1_struct_0(A_1022), k5_tmap_1(A_1022, B_1023))=k6_tmap_1(A_1022, B_1023) | ~m1_subset_1(B_1023, k1_zfmisc_1(u1_struct_0(A_1022))) | ~l1_pre_topc(A_1022) | ~v2_pre_topc(A_1022) | v2_struct_0(A_1022))), inference(cnfTransformation, [status(thm)], [f_133])).
% 50.68/35.57  tff(c_45454, plain, (![A_1022, A_1]: (g1_pre_topc(u1_struct_0(A_1022), k5_tmap_1(A_1022, A_1))=k6_tmap_1(A_1022, A_1) | ~l1_pre_topc(A_1022) | ~v2_pre_topc(A_1022) | v2_struct_0(A_1022) | ~r1_tarski(A_1, u1_struct_0(A_1022)))), inference(resolution, [status(thm)], [c_4, c_45442])).
% 50.68/35.57  tff(c_159827, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_159806, c_45454])).
% 50.68/35.57  tff(c_159850, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', u1_struct_0('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159128, c_78, c_76, c_159827])).
% 50.68/35.57  tff(c_159851, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_159850])).
% 50.68/35.57  tff(c_44938, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k8_tmap_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 50.68/35.57  tff(c_160096, plain, (k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))!=k8_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_159851, c_44938])).
% 50.68/35.57  tff(c_210377, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_209675, c_160096])).
% 50.68/35.57  tff(c_210926, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_210377])).
% 50.68/35.57  tff(c_210928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_210926])).
% 50.68/35.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.68/35.57  
% 50.68/35.57  Inference rules
% 50.68/35.57  ----------------------
% 50.68/35.57  #Ref     : 80
% 50.68/35.57  #Sup     : 52932
% 50.68/35.57  #Fact    : 0
% 50.68/35.57  #Define  : 0
% 50.68/35.57  #Split   : 108
% 50.68/35.57  #Chain   : 0
% 50.68/35.57  #Close   : 0
% 50.68/35.57  
% 50.68/35.57  Ordering : KBO
% 50.68/35.57  
% 50.68/35.57  Simplification rules
% 50.68/35.57  ----------------------
% 50.68/35.57  #Subsume      : 9838
% 50.68/35.57  #Demod        : 63765
% 50.68/35.57  #Tautology    : 9530
% 50.68/35.57  #SimpNegUnit  : 5238
% 50.68/35.57  #BackRed      : 342
% 50.68/35.57  
% 50.68/35.57  #Partial instantiations: 0
% 50.68/35.57  #Strategies tried      : 1
% 50.68/35.57  
% 50.68/35.57  Timing (in seconds)
% 50.68/35.57  ----------------------
% 50.68/35.57  Preprocessing        : 0.39
% 50.68/35.57  Parsing              : 0.21
% 50.68/35.57  CNF conversion       : 0.03
% 50.68/35.57  Main loop            : 34.33
% 50.68/35.57  Inferencing          : 5.52
% 50.68/35.57  Reduction            : 12.45
% 50.68/35.57  Demodulation         : 9.40
% 50.68/35.57  BG Simplification    : 0.79
% 50.68/35.57  Subsumption          : 13.15
% 50.68/35.57  Abstraction          : 1.05
% 50.68/35.57  MUC search           : 0.00
% 50.68/35.57  Cooper               : 0.00
% 50.68/35.57  Total                : 34.84
% 50.68/35.57  Index Insertion      : 0.00
% 50.68/35.57  Index Deletion       : 0.00
% 50.68/35.57  Index Matching       : 0.00
% 50.68/35.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
