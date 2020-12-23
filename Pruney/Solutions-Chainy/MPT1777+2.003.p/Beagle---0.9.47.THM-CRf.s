%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:32 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  150 (2684 expanded)
%              Number of leaves         :   50 ( 935 expanded)
%              Depth                    :   25
%              Number of atoms          :  327 (12122 expanded)
%              Number of equality atoms :   38 (1584 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_258,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_209,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_86,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_72,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_128,plain,(
    ! [B_428,A_429] :
      ( l1_pre_topc(B_428)
      | ~ m1_pre_topc(B_428,A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_137,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_128])).

tff(c_144,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_137])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_105,plain,(
    ! [A_426] :
      ( u1_struct_0(A_426) = k2_struct_0(A_426)
      | ~ l1_struct_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_109,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_152,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_109])).

tff(c_172,plain,(
    ! [A_432] :
      ( ~ v1_xboole_0(u1_struct_0(A_432))
      | ~ l1_struct_0(A_432)
      | v2_struct_0(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_172])).

tff(c_185,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_175])).

tff(c_189,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_192,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_189])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_192])).

tff(c_197,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_162,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_62])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_386,plain,(
    ! [B_446,A_447] :
      ( v2_pre_topc(B_446)
      | ~ m1_pre_topc(B_446,A_447)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_395,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_386])).

tff(c_402,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_395])).

tff(c_42,plain,(
    ! [A_32] :
      ( v3_pre_topc(k2_struct_0(A_32),A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_54,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_82,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_80,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_76,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_110,plain,(
    ! [A_427] :
      ( u1_struct_0(A_427) = k2_struct_0(A_427)
      | ~ l1_pre_topc(A_427) ) ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_118,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_110])).

tff(c_68,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_123,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68])).

tff(c_161,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_123])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_159,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_66])).

tff(c_160,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_159])).

tff(c_134,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_128])).

tff(c_141,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_134])).

tff(c_46,plain,(
    ! [A_40] :
      ( m1_pre_topc(A_40,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_148,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_109])).

tff(c_64,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_153,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_64])).

tff(c_297,plain,(
    ! [A_445] :
      ( m1_subset_1(u1_pre_topc(A_445),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_445))))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_309,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_297])).

tff(c_321,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_309])).

tff(c_474,plain,(
    ! [A_450,B_451] :
      ( v1_pre_topc(g1_pre_topc(A_450,B_451))
      | ~ m1_subset_1(B_451,k1_zfmisc_1(k1_zfmisc_1(A_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_477,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_321,c_474])).

tff(c_495,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_477])).

tff(c_501,plain,(
    ! [A_452] :
      ( g1_pre_topc(u1_struct_0(A_452),u1_pre_topc(A_452)) = A_452
      | ~ v1_pre_topc(A_452)
      | ~ l1_pre_topc(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_513,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_501])).

tff(c_526,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_513])).

tff(c_614,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_526])).

tff(c_645,plain,(
    ! [D_465,B_466,C_467,A_468] :
      ( D_465 = B_466
      | g1_pre_topc(C_467,D_465) != g1_pre_topc(A_468,B_466)
      | ~ m1_subset_1(B_466,k1_zfmisc_1(k1_zfmisc_1(A_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_657,plain,(
    ! [D_465,C_467] :
      ( u1_pre_topc('#skF_3') = D_465
      | g1_pre_topc(C_467,D_465) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_645])).

tff(c_662,plain,(
    ! [D_469,C_470] :
      ( u1_pre_topc('#skF_3') = D_469
      | g1_pre_topc(C_470,D_469) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_657])).

tff(c_672,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_662])).

tff(c_678,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_153])).

tff(c_306,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_297])).

tff(c_319,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_306])).

tff(c_815,plain,(
    ! [C_481,A_482,D_483,B_484] :
      ( C_481 = A_482
      | g1_pre_topc(C_481,D_483) != g1_pre_topc(A_482,B_484)
      | ~ m1_subset_1(B_484,k1_zfmisc_1(k1_zfmisc_1(A_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_823,plain,(
    ! [C_481,D_483] :
      ( k2_struct_0('#skF_4') = C_481
      | g1_pre_topc(C_481,D_483) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_815])).

tff(c_832,plain,(
    ! [C_485,D_486] :
      ( k2_struct_0('#skF_4') = C_485
      | g1_pre_topc(C_485,D_486) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_823])).

tff(c_842,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_832])).

tff(c_850,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_148])).

tff(c_1102,plain,(
    ! [A_496,B_497] :
      ( m1_pre_topc(A_496,g1_pre_topc(u1_struct_0(B_497),u1_pre_topc(B_497)))
      | ~ m1_pre_topc(A_496,B_497)
      | ~ l1_pre_topc(B_497)
      | ~ l1_pre_topc(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1126,plain,(
    ! [A_496] :
      ( m1_pre_topc(A_496,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_496,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_1102])).

tff(c_1158,plain,(
    ! [A_498] :
      ( m1_pre_topc(A_498,'#skF_4')
      | ~ m1_pre_topc(A_498,'#skF_3')
      | ~ l1_pre_topc(A_498) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_614,c_850,c_1126])).

tff(c_1169,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1158])).

tff(c_1176,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1169])).

tff(c_58,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_56,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_92,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56])).

tff(c_1370,plain,(
    ! [F_520,B_521,D_517,E_519,A_518,C_516,H_522] :
      ( r1_tmap_1(D_517,B_521,E_519,H_522)
      | ~ r1_tmap_1(C_516,B_521,k3_tmap_1(A_518,B_521,D_517,C_516,E_519),H_522)
      | ~ m1_connsp_2(F_520,D_517,H_522)
      | ~ r1_tarski(F_520,u1_struct_0(C_516))
      | ~ m1_subset_1(H_522,u1_struct_0(C_516))
      | ~ m1_subset_1(H_522,u1_struct_0(D_517))
      | ~ m1_subset_1(F_520,k1_zfmisc_1(u1_struct_0(D_517)))
      | ~ m1_pre_topc(C_516,D_517)
      | ~ m1_subset_1(E_519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_517),u1_struct_0(B_521))))
      | ~ v1_funct_2(E_519,u1_struct_0(D_517),u1_struct_0(B_521))
      | ~ v1_funct_1(E_519)
      | ~ m1_pre_topc(D_517,A_518)
      | v2_struct_0(D_517)
      | ~ m1_pre_topc(C_516,A_518)
      | v2_struct_0(C_516)
      | ~ l1_pre_topc(B_521)
      | ~ v2_pre_topc(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_1372,plain,(
    ! [F_520] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_520,'#skF_4','#skF_6')
      | ~ r1_tarski(F_520,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_520,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_92,c_1370])).

tff(c_1375,plain,(
    ! [F_520] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_520,'#skF_4','#skF_6')
      | ~ r1_tarski(F_520,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(F_520,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_76,c_72,c_70,c_161,c_118,c_152,c_160,c_118,c_152,c_1176,c_152,c_162,c_152,c_162,c_850,c_850,c_1372])).

tff(c_1386,plain,(
    ! [F_527] :
      ( ~ m1_connsp_2(F_527,'#skF_4','#skF_6')
      | ~ r1_tarski(F_527,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(F_527,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_78,c_74,c_54,c_1375])).

tff(c_1396,plain,(
    ! [A_528] :
      ( ~ m1_connsp_2(A_528,'#skF_4','#skF_6')
      | ~ r1_tarski(A_528,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1386])).

tff(c_1401,plain,(
    ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1396])).

tff(c_1315,plain,(
    ! [B_506,A_507,C_508] :
      ( m1_connsp_2(B_506,A_507,C_508)
      | ~ r2_hidden(C_508,B_506)
      | ~ v3_pre_topc(B_506,A_507)
      | ~ m1_subset_1(C_508,u1_struct_0(A_507))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(u1_struct_0(A_507)))
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1321,plain,(
    ! [B_506,C_508] :
      ( m1_connsp_2(B_506,'#skF_4',C_508)
      | ~ r2_hidden(C_508,B_506)
      | ~ v3_pre_topc(B_506,'#skF_4')
      | ~ m1_subset_1(C_508,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_1315])).

tff(c_1332,plain,(
    ! [B_506,C_508] :
      ( m1_connsp_2(B_506,'#skF_4',C_508)
      | ~ r2_hidden(C_508,B_506)
      | ~ v3_pre_topc(B_506,'#skF_4')
      | ~ m1_subset_1(C_508,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_144,c_152,c_1321])).

tff(c_1360,plain,(
    ! [B_512,C_513] :
      ( m1_connsp_2(B_512,'#skF_4',C_513)
      | ~ r2_hidden(C_513,B_512)
      | ~ v3_pre_topc(B_512,'#skF_4')
      | ~ m1_subset_1(C_513,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_512,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1332])).

tff(c_1971,plain,(
    ! [B_561] :
      ( m1_connsp_2(B_561,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_561)
      | ~ v3_pre_topc(B_561,'#skF_4')
      | ~ m1_subset_1(B_561,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_162,c_1360])).

tff(c_2365,plain,(
    ! [A_578] :
      ( m1_connsp_2(A_578,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',A_578)
      | ~ v3_pre_topc(A_578,'#skF_4')
      | ~ r1_tarski(A_578,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1971])).

tff(c_2369,plain,
    ( m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2365])).

tff(c_2372,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1401,c_2369])).

tff(c_2373,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2372])).

tff(c_2376,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2373])).

tff(c_2380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_144,c_2376])).

tff(c_2381,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2372])).

tff(c_2385,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_2381])).

tff(c_2388,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_2385])).

tff(c_2390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_2388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.93  
% 4.85/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.93  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.85/1.93  
% 4.85/1.93  %Foreground sorts:
% 4.85/1.93  
% 4.85/1.93  
% 4.85/1.93  %Background operators:
% 4.85/1.93  
% 4.85/1.93  
% 4.85/1.93  %Foreground operators:
% 4.85/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.85/1.93  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.85/1.93  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.85/1.93  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.85/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.85/1.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.85/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.93  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.85/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/1.93  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.85/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.85/1.93  tff('#skF_7', type, '#skF_7': $i).
% 4.85/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.85/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.85/1.93  tff('#skF_6', type, '#skF_6': $i).
% 4.85/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.85/1.93  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.85/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.85/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.85/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.85/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.85/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.85/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.85/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.85/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.93  
% 5.22/1.95  tff(f_258, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.22/1.95  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.22/1.95  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.22/1.95  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.22/1.95  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.22/1.95  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.22/1.95  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.22/1.95  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.22/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.22/1.95  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.22/1.95  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.22/1.95  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.22/1.95  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 5.22/1.95  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.22/1.95  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.22/1.95  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.22/1.95  tff(f_209, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.22/1.95  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.22/1.95  tff(c_86, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_72, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_128, plain, (![B_428, A_429]: (l1_pre_topc(B_428) | ~m1_pre_topc(B_428, A_429) | ~l1_pre_topc(A_429))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.22/1.95  tff(c_137, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_128])).
% 5.22/1.95  tff(c_144, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_137])).
% 5.22/1.95  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.22/1.95  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_105, plain, (![A_426]: (u1_struct_0(A_426)=k2_struct_0(A_426) | ~l1_struct_0(A_426))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.22/1.95  tff(c_109, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_26, c_105])).
% 5.22/1.95  tff(c_152, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_144, c_109])).
% 5.22/1.95  tff(c_172, plain, (![A_432]: (~v1_xboole_0(u1_struct_0(A_432)) | ~l1_struct_0(A_432) | v2_struct_0(A_432))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.22/1.95  tff(c_175, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152, c_172])).
% 5.22/1.95  tff(c_185, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_175])).
% 5.22/1.95  tff(c_189, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_185])).
% 5.22/1.95  tff(c_192, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_189])).
% 5.22/1.95  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_192])).
% 5.22/1.95  tff(c_197, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_185])).
% 5.22/1.95  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_162, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_62])).
% 5.22/1.95  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.22/1.95  tff(c_88, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_386, plain, (![B_446, A_447]: (v2_pre_topc(B_446) | ~m1_pre_topc(B_446, A_447) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.22/1.95  tff(c_395, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_386])).
% 5.22/1.95  tff(c_402, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_395])).
% 5.22/1.95  tff(c_42, plain, (![A_32]: (v3_pre_topc(k2_struct_0(A_32), A_32) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.22/1.95  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.22/1.95  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.22/1.95  tff(c_90, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_84, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_54, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_82, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_80, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_76, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_110, plain, (![A_427]: (u1_struct_0(A_427)=k2_struct_0(A_427) | ~l1_pre_topc(A_427))), inference(resolution, [status(thm)], [c_26, c_105])).
% 5.22/1.95  tff(c_118, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_110])).
% 5.22/1.95  tff(c_68, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_123, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_68])).
% 5.22/1.95  tff(c_161, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_123])).
% 5.22/1.95  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_159, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_66])).
% 5.22/1.95  tff(c_160, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_159])).
% 5.22/1.95  tff(c_134, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_128])).
% 5.22/1.95  tff(c_141, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_134])).
% 5.22/1.95  tff(c_46, plain, (![A_40]: (m1_pre_topc(A_40, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.22/1.95  tff(c_148, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_141, c_109])).
% 5.22/1.95  tff(c_64, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_153, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_64])).
% 5.22/1.95  tff(c_297, plain, (![A_445]: (m1_subset_1(u1_pre_topc(A_445), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_445)))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.22/1.95  tff(c_309, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_148, c_297])).
% 5.22/1.95  tff(c_321, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_309])).
% 5.22/1.95  tff(c_474, plain, (![A_450, B_451]: (v1_pre_topc(g1_pre_topc(A_450, B_451)) | ~m1_subset_1(B_451, k1_zfmisc_1(k1_zfmisc_1(A_450))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.22/1.95  tff(c_477, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_321, c_474])).
% 5.22/1.95  tff(c_495, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_477])).
% 5.22/1.95  tff(c_501, plain, (![A_452]: (g1_pre_topc(u1_struct_0(A_452), u1_pre_topc(A_452))=A_452 | ~v1_pre_topc(A_452) | ~l1_pre_topc(A_452))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.22/1.95  tff(c_513, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152, c_501])).
% 5.22/1.95  tff(c_526, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_513])).
% 5.22/1.95  tff(c_614, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_526])).
% 5.22/1.95  tff(c_645, plain, (![D_465, B_466, C_467, A_468]: (D_465=B_466 | g1_pre_topc(C_467, D_465)!=g1_pre_topc(A_468, B_466) | ~m1_subset_1(B_466, k1_zfmisc_1(k1_zfmisc_1(A_468))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.22/1.95  tff(c_657, plain, (![D_465, C_467]: (u1_pre_topc('#skF_3')=D_465 | g1_pre_topc(C_467, D_465)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_153, c_645])).
% 5.22/1.95  tff(c_662, plain, (![D_469, C_470]: (u1_pre_topc('#skF_3')=D_469 | g1_pre_topc(C_470, D_469)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_657])).
% 5.22/1.95  tff(c_672, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_614, c_662])).
% 5.22/1.95  tff(c_678, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_672, c_153])).
% 5.22/1.95  tff(c_306, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152, c_297])).
% 5.22/1.95  tff(c_319, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_306])).
% 5.22/1.95  tff(c_815, plain, (![C_481, A_482, D_483, B_484]: (C_481=A_482 | g1_pre_topc(C_481, D_483)!=g1_pre_topc(A_482, B_484) | ~m1_subset_1(B_484, k1_zfmisc_1(k1_zfmisc_1(A_482))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.22/1.95  tff(c_823, plain, (![C_481, D_483]: (k2_struct_0('#skF_4')=C_481 | g1_pre_topc(C_481, D_483)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_614, c_815])).
% 5.22/1.95  tff(c_832, plain, (![C_485, D_486]: (k2_struct_0('#skF_4')=C_485 | g1_pre_topc(C_485, D_486)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_823])).
% 5.22/1.95  tff(c_842, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_678, c_832])).
% 5.22/1.95  tff(c_850, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_148])).
% 5.22/1.95  tff(c_1102, plain, (![A_496, B_497]: (m1_pre_topc(A_496, g1_pre_topc(u1_struct_0(B_497), u1_pre_topc(B_497))) | ~m1_pre_topc(A_496, B_497) | ~l1_pre_topc(B_497) | ~l1_pre_topc(A_496))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.22/1.95  tff(c_1126, plain, (![A_496]: (m1_pre_topc(A_496, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_496, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_496))), inference(superposition, [status(thm), theory('equality')], [c_672, c_1102])).
% 5.22/1.95  tff(c_1158, plain, (![A_498]: (m1_pre_topc(A_498, '#skF_4') | ~m1_pre_topc(A_498, '#skF_3') | ~l1_pre_topc(A_498))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_614, c_850, c_1126])).
% 5.22/1.95  tff(c_1169, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1158])).
% 5.22/1.95  tff(c_1176, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1169])).
% 5.22/1.95  tff(c_58, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_56, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_258])).
% 5.22/1.95  tff(c_92, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56])).
% 5.22/1.95  tff(c_1370, plain, (![F_520, B_521, D_517, E_519, A_518, C_516, H_522]: (r1_tmap_1(D_517, B_521, E_519, H_522) | ~r1_tmap_1(C_516, B_521, k3_tmap_1(A_518, B_521, D_517, C_516, E_519), H_522) | ~m1_connsp_2(F_520, D_517, H_522) | ~r1_tarski(F_520, u1_struct_0(C_516)) | ~m1_subset_1(H_522, u1_struct_0(C_516)) | ~m1_subset_1(H_522, u1_struct_0(D_517)) | ~m1_subset_1(F_520, k1_zfmisc_1(u1_struct_0(D_517))) | ~m1_pre_topc(C_516, D_517) | ~m1_subset_1(E_519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_517), u1_struct_0(B_521)))) | ~v1_funct_2(E_519, u1_struct_0(D_517), u1_struct_0(B_521)) | ~v1_funct_1(E_519) | ~m1_pre_topc(D_517, A_518) | v2_struct_0(D_517) | ~m1_pre_topc(C_516, A_518) | v2_struct_0(C_516) | ~l1_pre_topc(B_521) | ~v2_pre_topc(B_521) | v2_struct_0(B_521) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518))), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.22/1.95  tff(c_1372, plain, (![F_520]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_520, '#skF_4', '#skF_6') | ~r1_tarski(F_520, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_520, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_92, c_1370])).
% 5.22/1.95  tff(c_1375, plain, (![F_520]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_520, '#skF_4', '#skF_6') | ~r1_tarski(F_520, k2_struct_0('#skF_4')) | ~m1_subset_1(F_520, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_80, c_76, c_72, c_70, c_161, c_118, c_152, c_160, c_118, c_152, c_1176, c_152, c_162, c_152, c_162, c_850, c_850, c_1372])).
% 5.22/1.95  tff(c_1386, plain, (![F_527]: (~m1_connsp_2(F_527, '#skF_4', '#skF_6') | ~r1_tarski(F_527, k2_struct_0('#skF_4')) | ~m1_subset_1(F_527, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_78, c_74, c_54, c_1375])).
% 5.22/1.95  tff(c_1396, plain, (![A_528]: (~m1_connsp_2(A_528, '#skF_4', '#skF_6') | ~r1_tarski(A_528, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1386])).
% 5.22/1.95  tff(c_1401, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_1396])).
% 5.22/1.95  tff(c_1315, plain, (![B_506, A_507, C_508]: (m1_connsp_2(B_506, A_507, C_508) | ~r2_hidden(C_508, B_506) | ~v3_pre_topc(B_506, A_507) | ~m1_subset_1(C_508, u1_struct_0(A_507)) | ~m1_subset_1(B_506, k1_zfmisc_1(u1_struct_0(A_507))) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.22/1.95  tff(c_1321, plain, (![B_506, C_508]: (m1_connsp_2(B_506, '#skF_4', C_508) | ~r2_hidden(C_508, B_506) | ~v3_pre_topc(B_506, '#skF_4') | ~m1_subset_1(C_508, k2_struct_0('#skF_4')) | ~m1_subset_1(B_506, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_1315])).
% 5.22/1.95  tff(c_1332, plain, (![B_506, C_508]: (m1_connsp_2(B_506, '#skF_4', C_508) | ~r2_hidden(C_508, B_506) | ~v3_pre_topc(B_506, '#skF_4') | ~m1_subset_1(C_508, k2_struct_0('#skF_4')) | ~m1_subset_1(B_506, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_402, c_144, c_152, c_1321])).
% 5.22/1.95  tff(c_1360, plain, (![B_512, C_513]: (m1_connsp_2(B_512, '#skF_4', C_513) | ~r2_hidden(C_513, B_512) | ~v3_pre_topc(B_512, '#skF_4') | ~m1_subset_1(C_513, k2_struct_0('#skF_4')) | ~m1_subset_1(B_512, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_1332])).
% 5.22/1.95  tff(c_1971, plain, (![B_561]: (m1_connsp_2(B_561, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_561) | ~v3_pre_topc(B_561, '#skF_4') | ~m1_subset_1(B_561, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_162, c_1360])).
% 5.22/1.95  tff(c_2365, plain, (![A_578]: (m1_connsp_2(A_578, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', A_578) | ~v3_pre_topc(A_578, '#skF_4') | ~r1_tarski(A_578, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1971])).
% 5.22/1.95  tff(c_2369, plain, (m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6, c_2365])).
% 5.22/1.95  tff(c_2372, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1401, c_2369])).
% 5.22/1.95  tff(c_2373, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2372])).
% 5.22/1.95  tff(c_2376, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2373])).
% 5.22/1.95  tff(c_2380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_144, c_2376])).
% 5.22/1.95  tff(c_2381, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2372])).
% 5.22/1.95  tff(c_2385, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_2381])).
% 5.22/1.95  tff(c_2388, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_2385])).
% 5.22/1.95  tff(c_2390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_2388])).
% 5.22/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/1.95  
% 5.22/1.95  Inference rules
% 5.22/1.95  ----------------------
% 5.22/1.95  #Ref     : 6
% 5.22/1.95  #Sup     : 462
% 5.22/1.95  #Fact    : 0
% 5.22/1.95  #Define  : 0
% 5.22/1.95  #Split   : 19
% 5.22/1.95  #Chain   : 0
% 5.22/1.95  #Close   : 0
% 5.22/1.95  
% 5.22/1.95  Ordering : KBO
% 5.22/1.95  
% 5.22/1.95  Simplification rules
% 5.22/1.95  ----------------------
% 5.22/1.95  #Subsume      : 56
% 5.22/1.95  #Demod        : 647
% 5.22/1.95  #Tautology    : 180
% 5.22/1.95  #SimpNegUnit  : 14
% 5.22/1.95  #BackRed      : 18
% 5.22/1.95  
% 5.22/1.95  #Partial instantiations: 0
% 5.22/1.95  #Strategies tried      : 1
% 5.22/1.95  
% 5.22/1.95  Timing (in seconds)
% 5.22/1.95  ----------------------
% 5.22/1.96  Preprocessing        : 0.42
% 5.22/1.96  Parsing              : 0.22
% 5.22/1.96  CNF conversion       : 0.06
% 5.22/1.96  Main loop            : 0.73
% 5.22/1.96  Inferencing          : 0.24
% 5.22/1.96  Reduction            : 0.27
% 5.22/1.96  Demodulation         : 0.20
% 5.22/1.96  BG Simplification    : 0.03
% 5.22/1.96  Subsumption          : 0.12
% 5.22/1.96  Abstraction          : 0.03
% 5.22/1.96  MUC search           : 0.00
% 5.22/1.96  Cooper               : 0.00
% 5.22/1.96  Total                : 1.19
% 5.22/1.96  Index Insertion      : 0.00
% 5.22/1.96  Index Deletion       : 0.00
% 5.22/1.96  Index Matching       : 0.00
% 5.22/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
