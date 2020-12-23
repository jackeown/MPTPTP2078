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
% DateTime   : Thu Dec  3 10:19:16 EST 2020

% Result     : Theorem 9.49s
% Output     : CNFRefutation 9.60s
% Verified   : 
% Statistics : Number of formulae       :  166 (1515 expanded)
%              Number of leaves         :   38 ( 539 expanded)
%              Depth                    :   18
%              Number of atoms          :  497 (7612 expanded)
%              Number of equality atoms :   22 ( 570 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

tff(c_96,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_98,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_5] :
      ( r2_hidden(u1_struct_0(A_5),u1_pre_topc(A_5))
      | ~ v2_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6465,plain,(
    ! [B_290,A_291] :
      ( v3_pre_topc(B_290,A_291)
      | ~ r2_hidden(B_290,u1_pre_topc(A_291))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6471,plain,(
    ! [A_292,A_293] :
      ( v3_pre_topc(A_292,A_293)
      | ~ r2_hidden(A_292,u1_pre_topc(A_293))
      | ~ l1_pre_topc(A_293)
      | ~ r1_tarski(A_292,u1_struct_0(A_293)) ) ),
    inference(resolution,[status(thm)],[c_10,c_6465])).

tff(c_6474,plain,(
    ! [A_5] :
      ( v3_pre_topc(u1_struct_0(A_5),A_5)
      | ~ r1_tarski(u1_struct_0(A_5),u1_struct_0(A_5))
      | ~ v2_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_46,c_6471])).

tff(c_6477,plain,(
    ! [A_5] :
      ( v3_pre_topc(u1_struct_0(A_5),A_5)
      | ~ v2_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6474])).

tff(c_56,plain,(
    ! [A_24] :
      ( m1_subset_1(u1_pre_topc(A_24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_24))))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_171,plain,(
    ! [A_86,B_87] :
      ( l1_pre_topc(g1_pre_topc(A_86,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_179,plain,(
    ! [A_24] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_56,c_171])).

tff(c_58,plain,(
    ! [A_25] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_25),u1_pre_topc(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_100,plain,
    ( ~ v5_pre_topc('#skF_7',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_108,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_100])).

tff(c_196,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_90,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_88,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_92,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_94,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_204,plain,(
    ! [B_98,A_99] :
      ( v3_pre_topc(B_98,A_99)
      | ~ r2_hidden(B_98,u1_pre_topc(A_99))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_214,plain,(
    ! [A_100,A_101] :
      ( v3_pre_topc(A_100,A_101)
      | ~ r2_hidden(A_100,u1_pre_topc(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ r1_tarski(A_100,u1_struct_0(A_101)) ) ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_220,plain,(
    ! [A_5] :
      ( v3_pre_topc(u1_struct_0(A_5),A_5)
      | ~ r1_tarski(u1_struct_0(A_5),u1_struct_0(A_5))
      | ~ v2_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_46,c_214])).

tff(c_224,plain,(
    ! [A_5] :
      ( v3_pre_topc(u1_struct_0(A_5),A_5)
      | ~ v2_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_220])).

tff(c_82,plain,(
    v1_funct_2('#skF_7',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_110,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v5_pre_topc('#skF_7',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_107,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_106])).

tff(c_229,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_107])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_111,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_80])).

tff(c_958,plain,(
    ! [D_197,A_198,B_199] :
      ( v5_pre_topc(D_197,A_198,B_199)
      | ~ v5_pre_topc(D_197,g1_pre_topc(u1_struct_0(A_198),u1_pre_topc(A_198)),B_199)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_198),u1_pre_topc(A_198))),u1_struct_0(B_199))))
      | ~ v1_funct_2(D_197,u1_struct_0(g1_pre_topc(u1_struct_0(A_198),u1_pre_topc(A_198))),u1_struct_0(B_199))
      | ~ m1_subset_1(D_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_198),u1_struct_0(B_199))))
      | ~ v1_funct_2(D_197,u1_struct_0(A_198),u1_struct_0(B_199))
      | ~ v1_funct_1(D_197)
      | ~ l1_pre_topc(B_199)
      | ~ v2_pre_topc(B_199)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_961,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_958])).

tff(c_968,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_90,c_110,c_229,c_961])).

tff(c_993,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_996,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_993])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_996])).

tff(c_1002,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_673,plain,(
    ! [B_163,A_164] :
      ( m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_164),u1_pre_topc(A_164)))))
      | ~ v3_pre_topc(B_163,g1_pre_topc(u1_struct_0(A_164),u1_pre_topc(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_713,plain,(
    ! [A_165,A_166] :
      ( m1_subset_1(A_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v3_pre_topc(A_165,g1_pre_topc(u1_struct_0(A_166),u1_pre_topc(A_166)))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | ~ r1_tarski(A_165,u1_struct_0(g1_pre_topc(u1_struct_0(A_166),u1_pre_topc(A_166)))) ) ),
    inference(resolution,[status(thm)],[c_10,c_673])).

tff(c_757,plain,(
    ! [A_177] :
      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177))),k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177))),g1_pre_topc(u1_struct_0(A_177),u1_pre_topc(A_177)))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_6,c_713])).

tff(c_767,plain,(
    ! [A_178] :
      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))) ) ),
    inference(resolution,[status(thm)],[c_224,c_757])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_789,plain,(
    ! [A_178] :
      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))),u1_struct_0(A_178))
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_178),u1_pre_topc(A_178))) ) ),
    inference(resolution,[status(thm)],[c_767,c_8])).

tff(c_324,plain,(
    ! [B_115,A_116] :
      ( m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_116),u1_pre_topc(A_116)))))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ v3_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_337,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(B_117,u1_struct_0(g1_pre_topc(u1_struct_0(A_118),u1_pre_topc(A_118))))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ v3_pre_topc(B_117,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_324,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_824,plain,(
    ! [A_183,B_184] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183))) = B_184
      | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_183),u1_pre_topc(A_183))),B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ v3_pre_topc(B_184,A_183)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183) ) ),
    inference(resolution,[status(thm)],[c_337,c_2])).

tff(c_981,plain,(
    ! [A_202] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_202),u1_pre_topc(A_202))) = u1_struct_0(A_202)
      | ~ m1_subset_1(u1_struct_0(A_202),k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ v3_pre_topc(u1_struct_0(A_202),A_202)
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_202),u1_pre_topc(A_202)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_202),u1_pre_topc(A_202))) ) ),
    inference(resolution,[status(thm)],[c_789,c_824])).

tff(c_988,plain,(
    ! [A_202] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_202),u1_pre_topc(A_202))) = u1_struct_0(A_202)
      | ~ v3_pre_topc(u1_struct_0(A_202),A_202)
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_202),u1_pre_topc(A_202)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_202),u1_pre_topc(A_202)))
      | ~ r1_tarski(u1_struct_0(A_202),u1_struct_0(A_202)) ) ),
    inference(resolution,[status(thm)],[c_10,c_981])).

tff(c_1003,plain,(
    ! [A_203] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_203),u1_pre_topc(A_203))) = u1_struct_0(A_203)
      | ~ v3_pre_topc(u1_struct_0(A_203),A_203)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_203),u1_pre_topc(A_203)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_203),u1_pre_topc(A_203))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_988])).

tff(c_1006,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1002,c_1003])).

tff(c_1012,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_1006])).

tff(c_1014,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1012])).

tff(c_1017,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_1014])).

tff(c_1021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1017])).

tff(c_1022,plain,
    ( ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5')
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1012])).

tff(c_1036,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1022])).

tff(c_1039,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_224,c_1036])).

tff(c_1043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_94,c_1039])).

tff(c_1044,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1022])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1023,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1012])).

tff(c_1001,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_1047,plain,
    ( ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1001])).

tff(c_1048,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(splitLeft,[status(thm)],[c_1047])).

tff(c_1784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1044,c_1048])).

tff(c_1785,plain,
    ( ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1047])).

tff(c_2671,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1044,c_1785])).

tff(c_2407,plain,(
    ! [D_213,A_214,B_215] :
      ( v5_pre_topc(D_213,A_214,B_215)
      | ~ v5_pre_topc(D_213,A_214,g1_pre_topc(u1_struct_0(B_215),u1_pre_topc(B_215)))
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0(g1_pre_topc(u1_struct_0(B_215),u1_pre_topc(B_215))))))
      | ~ v1_funct_2(D_213,u1_struct_0(A_214),u1_struct_0(g1_pre_topc(u1_struct_0(B_215),u1_pre_topc(B_215))))
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0(B_215))))
      | ~ v1_funct_2(D_213,u1_struct_0(A_214),u1_struct_0(B_215))
      | ~ v1_funct_1(D_213)
      | ~ l1_pre_topc(B_215)
      | ~ v2_pre_topc(B_215)
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2416,plain,(
    ! [D_213,A_214] :
      ( v5_pre_topc(D_213,A_214,'#skF_5')
      | ~ v5_pre_topc(D_213,A_214,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(D_213,u1_struct_0(A_214),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(D_213,u1_struct_0(A_214),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(D_213)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_2407])).

tff(c_6420,plain,(
    ! [D_288,A_289] :
      ( v5_pre_topc(D_288,A_289,'#skF_5')
      | ~ v5_pre_topc(D_288,A_289,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(D_288,u1_struct_0(A_289),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(D_288)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_1044,c_2416])).

tff(c_6442,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_6420])).

tff(c_6456,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_90,c_88,c_2671,c_6442])).

tff(c_6458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_6456])).

tff(c_6459,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_7129,plain,(
    ! [D_387,A_388,B_389] :
      ( v5_pre_topc(D_387,A_388,g1_pre_topc(u1_struct_0(B_389),u1_pre_topc(B_389)))
      | ~ v5_pre_topc(D_387,A_388,B_389)
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388),u1_struct_0(g1_pre_topc(u1_struct_0(B_389),u1_pre_topc(B_389))))))
      | ~ v1_funct_2(D_387,u1_struct_0(A_388),u1_struct_0(g1_pre_topc(u1_struct_0(B_389),u1_pre_topc(B_389))))
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388),u1_struct_0(B_389))))
      | ~ v1_funct_2(D_387,u1_struct_0(A_388),u1_struct_0(B_389))
      | ~ v1_funct_1(D_387)
      | ~ l1_pre_topc(B_389)
      | ~ v2_pre_topc(B_389)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_7132,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_111,c_7129])).

tff(c_7139,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_110,c_7132])).

tff(c_7140,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6459,c_7139])).

tff(c_7271,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7140])).

tff(c_7274,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_7271])).

tff(c_7278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_7274])).

tff(c_7280,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7140])).

tff(c_6935,plain,(
    ! [B_356,A_357] :
      ( m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_357),u1_pre_topc(A_357)))))
      | ~ v3_pre_topc(B_356,g1_pre_topc(u1_struct_0(A_357),u1_pre_topc(A_357)))
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6976,plain,(
    ! [A_359,A_360] :
      ( m1_subset_1(A_359,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ v3_pre_topc(A_359,g1_pre_topc(u1_struct_0(A_360),u1_pre_topc(A_360)))
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | ~ r1_tarski(A_359,u1_struct_0(g1_pre_topc(u1_struct_0(A_360),u1_pre_topc(A_360)))) ) ),
    inference(resolution,[status(thm)],[c_10,c_6935])).

tff(c_7042,plain,(
    ! [A_376] :
      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_376),u1_pre_topc(A_376))),k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_376),u1_pre_topc(A_376))),g1_pre_topc(u1_struct_0(A_376),u1_pre_topc(A_376)))
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376) ) ),
    inference(resolution,[status(thm)],[c_6,c_6976])).

tff(c_7052,plain,(
    ! [A_377] :
      ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_377),u1_pre_topc(A_377))),k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_377),u1_pre_topc(A_377)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_377),u1_pre_topc(A_377))) ) ),
    inference(resolution,[status(thm)],[c_6477,c_7042])).

tff(c_7074,plain,(
    ! [A_377] :
      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_377),u1_pre_topc(A_377))),u1_struct_0(A_377))
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_377),u1_pre_topc(A_377)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_377),u1_pre_topc(A_377))) ) ),
    inference(resolution,[status(thm)],[c_7052,c_8])).

tff(c_6631,plain,(
    ! [B_318,A_319] :
      ( m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_319),u1_pre_topc(A_319)))))
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ v3_pre_topc(B_318,A_319)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6656,plain,(
    ! [B_321,A_322] :
      ( r1_tarski(B_321,u1_struct_0(g1_pre_topc(u1_struct_0(A_322),u1_pre_topc(A_322))))
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ v3_pre_topc(B_321,A_322)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322) ) ),
    inference(resolution,[status(thm)],[c_6631,c_8])).

tff(c_7107,plain,(
    ! [A_384,B_385] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_384),u1_pre_topc(A_384))) = B_385
      | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_384),u1_pre_topc(A_384))),B_385)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ v3_pre_topc(B_385,A_384)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384) ) ),
    inference(resolution,[status(thm)],[c_6656,c_2])).

tff(c_7259,plain,(
    ! [A_401] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401))) = u1_struct_0(A_401)
      | ~ m1_subset_1(u1_struct_0(A_401),k1_zfmisc_1(u1_struct_0(A_401)))
      | ~ v3_pre_topc(u1_struct_0(A_401),A_401)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401))) ) ),
    inference(resolution,[status(thm)],[c_7074,c_7107])).

tff(c_7266,plain,(
    ! [A_401] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401))) = u1_struct_0(A_401)
      | ~ v3_pre_topc(u1_struct_0(A_401),A_401)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_401),u1_pre_topc(A_401)))
      | ~ r1_tarski(u1_struct_0(A_401),u1_struct_0(A_401)) ) ),
    inference(resolution,[status(thm)],[c_10,c_7259])).

tff(c_7281,plain,(
    ! [A_402] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_402),u1_pre_topc(A_402))) = u1_struct_0(A_402)
      | ~ v3_pre_topc(u1_struct_0(A_402),A_402)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_402),u1_pre_topc(A_402)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_402),u1_pre_topc(A_402))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7266])).

tff(c_7284,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_7280,c_7281])).

tff(c_7290,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_7284])).

tff(c_7292,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7290])).

tff(c_7295,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_7292])).

tff(c_7299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_7295])).

tff(c_7300,plain,
    ( ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4')
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_7290])).

tff(c_7315,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7300])).

tff(c_7318,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6477,c_7315])).

tff(c_7322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_98,c_7318])).

tff(c_7323,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_7300])).

tff(c_7343,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_111])).

tff(c_7344,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_110])).

tff(c_7302,plain,(
    ! [D_403,A_404,B_405] :
      ( v5_pre_topc(D_403,g1_pre_topc(u1_struct_0(A_404),u1_pre_topc(A_404)),B_405)
      | ~ v5_pre_topc(D_403,A_404,B_405)
      | ~ m1_subset_1(D_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_404),u1_pre_topc(A_404))),u1_struct_0(B_405))))
      | ~ v1_funct_2(D_403,u1_struct_0(g1_pre_topc(u1_struct_0(A_404),u1_pre_topc(A_404))),u1_struct_0(B_405))
      | ~ m1_subset_1(D_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404),u1_struct_0(B_405))))
      | ~ v1_funct_2(D_403,u1_struct_0(A_404),u1_struct_0(B_405))
      | ~ v1_funct_1(D_403)
      | ~ l1_pre_topc(B_405)
      | ~ v2_pre_topc(B_405)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_7305,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_7302])).

tff(c_7312,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_90,c_110,c_7305])).

tff(c_7313,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6459,c_7312])).

tff(c_7325,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7313])).

tff(c_7328,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_7325])).

tff(c_7332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_7328])).

tff(c_7333,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_7313])).

tff(c_7934,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7333])).

tff(c_6460,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_76,plain,(
    ! [D_58,A_44,B_52] :
      ( v5_pre_topc(D_58,A_44,g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)))
      | ~ v5_pre_topc(D_58,A_44,B_52)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44),u1_struct_0(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52))))))
      | ~ v1_funct_2(D_58,u1_struct_0(A_44),u1_struct_0(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52))))
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44),u1_struct_0(B_52))))
      | ~ v1_funct_2(D_58,u1_struct_0(A_44),u1_struct_0(B_52))
      | ~ v1_funct_1(D_58)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_8017,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_7343,c_76])).

tff(c_8026,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_92,c_90,c_88,c_86,c_7344,c_6460,c_8017])).

tff(c_8028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7934,c_8026])).

tff(c_8029,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_7333])).

tff(c_8096,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_8029])).

tff(c_8099,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_8096])).

tff(c_8103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8099])).

tff(c_8104,plain,
    ( ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(splitRight,[status(thm)],[c_8029])).

tff(c_8136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7343,c_7344,c_8104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.49/3.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.49/3.47  
% 9.49/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.60/3.48  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 9.60/3.48  
% 9.60/3.48  %Foreground sorts:
% 9.60/3.48  
% 9.60/3.48  
% 9.60/3.48  %Background operators:
% 9.60/3.48  
% 9.60/3.48  
% 9.60/3.48  %Foreground operators:
% 9.60/3.48  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.60/3.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.60/3.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.60/3.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.60/3.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.60/3.48  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.60/3.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.60/3.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.60/3.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.60/3.48  tff('#skF_7', type, '#skF_7': $i).
% 9.60/3.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.60/3.48  tff('#skF_5', type, '#skF_5': $i).
% 9.60/3.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.60/3.48  tff('#skF_6', type, '#skF_6': $i).
% 9.60/3.48  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.60/3.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.60/3.48  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 9.60/3.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.60/3.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.60/3.48  tff('#skF_4', type, '#skF_4': $i).
% 9.60/3.48  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.60/3.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.60/3.48  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 9.60/3.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.60/3.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.60/3.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.60/3.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.60/3.48  
% 9.60/3.50  tff(f_188, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 9.60/3.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.60/3.50  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 9.60/3.50  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.60/3.50  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 9.60/3.50  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 9.60/3.50  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 9.60/3.50  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 9.60/3.50  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 9.60/3.50  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 9.60/3.50  tff(f_158, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 9.60/3.50  tff(c_96, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_98, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.60/3.50  tff(c_46, plain, (![A_5]: (r2_hidden(u1_struct_0(A_5), u1_pre_topc(A_5)) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.60/3.50  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.60/3.50  tff(c_6465, plain, (![B_290, A_291]: (v3_pre_topc(B_290, A_291) | ~r2_hidden(B_290, u1_pre_topc(A_291)) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.60/3.50  tff(c_6471, plain, (![A_292, A_293]: (v3_pre_topc(A_292, A_293) | ~r2_hidden(A_292, u1_pre_topc(A_293)) | ~l1_pre_topc(A_293) | ~r1_tarski(A_292, u1_struct_0(A_293)))), inference(resolution, [status(thm)], [c_10, c_6465])).
% 9.60/3.50  tff(c_6474, plain, (![A_5]: (v3_pre_topc(u1_struct_0(A_5), A_5) | ~r1_tarski(u1_struct_0(A_5), u1_struct_0(A_5)) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_46, c_6471])).
% 9.60/3.50  tff(c_6477, plain, (![A_5]: (v3_pre_topc(u1_struct_0(A_5), A_5) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6474])).
% 9.60/3.50  tff(c_56, plain, (![A_24]: (m1_subset_1(u1_pre_topc(A_24), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_24)))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.60/3.50  tff(c_171, plain, (![A_86, B_87]: (l1_pre_topc(g1_pre_topc(A_86, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_86))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.60/3.50  tff(c_179, plain, (![A_24]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24))) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_56, c_171])).
% 9.60/3.50  tff(c_58, plain, (![A_25]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_25), u1_pre_topc(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.60/3.50  tff(c_78, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_100, plain, (~v5_pre_topc('#skF_7', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_108, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_100])).
% 9.60/3.50  tff(c_196, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_108])).
% 9.60/3.50  tff(c_90, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_88, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_92, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_94, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_204, plain, (![B_98, A_99]: (v3_pre_topc(B_98, A_99) | ~r2_hidden(B_98, u1_pre_topc(A_99)) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.60/3.50  tff(c_214, plain, (![A_100, A_101]: (v3_pre_topc(A_100, A_101) | ~r2_hidden(A_100, u1_pre_topc(A_101)) | ~l1_pre_topc(A_101) | ~r1_tarski(A_100, u1_struct_0(A_101)))), inference(resolution, [status(thm)], [c_10, c_204])).
% 9.60/3.50  tff(c_220, plain, (![A_5]: (v3_pre_topc(u1_struct_0(A_5), A_5) | ~r1_tarski(u1_struct_0(A_5), u1_struct_0(A_5)) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_46, c_214])).
% 9.60/3.50  tff(c_224, plain, (![A_5]: (v3_pre_topc(u1_struct_0(A_5), A_5) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_220])).
% 9.60/3.50  tff(c_82, plain, (v1_funct_2('#skF_7', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_110, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82])).
% 9.60/3.50  tff(c_106, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v5_pre_topc('#skF_7', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_107, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_106])).
% 9.60/3.50  tff(c_229, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_196, c_107])).
% 9.60/3.50  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_111, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_80])).
% 9.60/3.50  tff(c_958, plain, (![D_197, A_198, B_199]: (v5_pre_topc(D_197, A_198, B_199) | ~v5_pre_topc(D_197, g1_pre_topc(u1_struct_0(A_198), u1_pre_topc(A_198)), B_199) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_198), u1_pre_topc(A_198))), u1_struct_0(B_199)))) | ~v1_funct_2(D_197, u1_struct_0(g1_pre_topc(u1_struct_0(A_198), u1_pre_topc(A_198))), u1_struct_0(B_199)) | ~m1_subset_1(D_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_198), u1_struct_0(B_199)))) | ~v1_funct_2(D_197, u1_struct_0(A_198), u1_struct_0(B_199)) | ~v1_funct_1(D_197) | ~l1_pre_topc(B_199) | ~v2_pre_topc(B_199) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.60/3.50  tff(c_961, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_111, c_958])).
% 9.60/3.50  tff(c_968, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_90, c_110, c_229, c_961])).
% 9.60/3.50  tff(c_993, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_968])).
% 9.60/3.50  tff(c_996, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_993])).
% 9.60/3.50  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_996])).
% 9.60/3.50  tff(c_1002, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_968])).
% 9.60/3.50  tff(c_673, plain, (![B_163, A_164]: (m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_164), u1_pre_topc(A_164))))) | ~v3_pre_topc(B_163, g1_pre_topc(u1_struct_0(A_164), u1_pre_topc(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.60/3.50  tff(c_713, plain, (![A_165, A_166]: (m1_subset_1(A_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~v3_pre_topc(A_165, g1_pre_topc(u1_struct_0(A_166), u1_pre_topc(A_166))) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | ~r1_tarski(A_165, u1_struct_0(g1_pre_topc(u1_struct_0(A_166), u1_pre_topc(A_166)))))), inference(resolution, [status(thm)], [c_10, c_673])).
% 9.60/3.50  tff(c_757, plain, (![A_177]: (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177))), k1_zfmisc_1(u1_struct_0(A_177))) | ~v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177))), g1_pre_topc(u1_struct_0(A_177), u1_pre_topc(A_177))) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177))), inference(resolution, [status(thm)], [c_6, c_713])).
% 9.60/3.50  tff(c_767, plain, (![A_178]: (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))), k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))))), inference(resolution, [status(thm)], [c_224, c_757])).
% 9.60/3.50  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.60/3.50  tff(c_789, plain, (![A_178]: (r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))), u1_struct_0(A_178)) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_178), u1_pre_topc(A_178))))), inference(resolution, [status(thm)], [c_767, c_8])).
% 9.60/3.50  tff(c_324, plain, (![B_115, A_116]: (m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_116), u1_pre_topc(A_116))))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~v3_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.60/3.50  tff(c_337, plain, (![B_117, A_118]: (r1_tarski(B_117, u1_struct_0(g1_pre_topc(u1_struct_0(A_118), u1_pre_topc(A_118)))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~v3_pre_topc(B_117, A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(resolution, [status(thm)], [c_324, c_8])).
% 9.60/3.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.60/3.50  tff(c_824, plain, (![A_183, B_184]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183)))=B_184 | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_183), u1_pre_topc(A_183))), B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~v3_pre_topc(B_184, A_183) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183))), inference(resolution, [status(thm)], [c_337, c_2])).
% 9.60/3.50  tff(c_981, plain, (![A_202]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_202), u1_pre_topc(A_202)))=u1_struct_0(A_202) | ~m1_subset_1(u1_struct_0(A_202), k1_zfmisc_1(u1_struct_0(A_202))) | ~v3_pre_topc(u1_struct_0(A_202), A_202) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_202), u1_pre_topc(A_202))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_202), u1_pre_topc(A_202))))), inference(resolution, [status(thm)], [c_789, c_824])).
% 9.60/3.50  tff(c_988, plain, (![A_202]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_202), u1_pre_topc(A_202)))=u1_struct_0(A_202) | ~v3_pre_topc(u1_struct_0(A_202), A_202) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_202), u1_pre_topc(A_202))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_202), u1_pre_topc(A_202))) | ~r1_tarski(u1_struct_0(A_202), u1_struct_0(A_202)))), inference(resolution, [status(thm)], [c_10, c_981])).
% 9.60/3.50  tff(c_1003, plain, (![A_203]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_203), u1_pre_topc(A_203)))=u1_struct_0(A_203) | ~v3_pre_topc(u1_struct_0(A_203), A_203) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_203), u1_pre_topc(A_203))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_203), u1_pre_topc(A_203))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_988])).
% 9.60/3.50  tff(c_1006, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))=u1_struct_0('#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(resolution, [status(thm)], [c_1002, c_1003])).
% 9.60/3.50  tff(c_1012, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))=u1_struct_0('#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_1006])).
% 9.60/3.50  tff(c_1014, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_1012])).
% 9.60/3.50  tff(c_1017, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_179, c_1014])).
% 9.60/3.50  tff(c_1021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_1017])).
% 9.60/3.50  tff(c_1022, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5') | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))=u1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1012])).
% 9.60/3.50  tff(c_1036, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1022])).
% 9.60/3.50  tff(c_1039, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_224, c_1036])).
% 9.60/3.50  tff(c_1043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_94, c_1039])).
% 9.60/3.50  tff(c_1044, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))=u1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1022])).
% 9.60/3.50  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.60/3.50  tff(c_1023, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_1012])).
% 9.60/3.50  tff(c_1001, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_968])).
% 9.60/3.50  tff(c_1047, plain, (~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1001])).
% 9.60/3.50  tff(c_1048, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(splitLeft, [status(thm)], [c_1047])).
% 9.60/3.50  tff(c_1784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1044, c_1048])).
% 9.60/3.50  tff(c_1785, plain, (~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_1047])).
% 9.60/3.50  tff(c_2671, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1044, c_1785])).
% 9.60/3.50  tff(c_2407, plain, (![D_213, A_214, B_215]: (v5_pre_topc(D_213, A_214, B_215) | ~v5_pre_topc(D_213, A_214, g1_pre_topc(u1_struct_0(B_215), u1_pre_topc(B_215))) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), u1_struct_0(g1_pre_topc(u1_struct_0(B_215), u1_pre_topc(B_215)))))) | ~v1_funct_2(D_213, u1_struct_0(A_214), u1_struct_0(g1_pre_topc(u1_struct_0(B_215), u1_pre_topc(B_215)))) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), u1_struct_0(B_215)))) | ~v1_funct_2(D_213, u1_struct_0(A_214), u1_struct_0(B_215)) | ~v1_funct_1(D_213) | ~l1_pre_topc(B_215) | ~v2_pre_topc(B_215) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.60/3.50  tff(c_2416, plain, (![D_213, A_214]: (v5_pre_topc(D_213, A_214, '#skF_5') | ~v5_pre_topc(D_213, A_214, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), u1_struct_0('#skF_5')))) | ~v1_funct_2(D_213, u1_struct_0(A_214), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), u1_struct_0('#skF_5')))) | ~v1_funct_2(D_213, u1_struct_0(A_214), u1_struct_0('#skF_5')) | ~v1_funct_1(D_213) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_2407])).
% 9.60/3.50  tff(c_6420, plain, (![D_288, A_289]: (v5_pre_topc(D_288, A_289, '#skF_5') | ~v5_pre_topc(D_288, A_289, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1(D_288, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289), u1_struct_0('#skF_5')))) | ~v1_funct_2(D_288, u1_struct_0(A_289), u1_struct_0('#skF_5')) | ~v1_funct_1(D_288) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_1044, c_2416])).
% 9.60/3.50  tff(c_6442, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_86, c_6420])).
% 9.60/3.50  tff(c_6456, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_90, c_88, c_2671, c_6442])).
% 9.60/3.50  tff(c_6458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_6456])).
% 9.60/3.50  tff(c_6459, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_108])).
% 9.60/3.50  tff(c_7129, plain, (![D_387, A_388, B_389]: (v5_pre_topc(D_387, A_388, g1_pre_topc(u1_struct_0(B_389), u1_pre_topc(B_389))) | ~v5_pre_topc(D_387, A_388, B_389) | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388), u1_struct_0(g1_pre_topc(u1_struct_0(B_389), u1_pre_topc(B_389)))))) | ~v1_funct_2(D_387, u1_struct_0(A_388), u1_struct_0(g1_pre_topc(u1_struct_0(B_389), u1_pre_topc(B_389)))) | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388), u1_struct_0(B_389)))) | ~v1_funct_2(D_387, u1_struct_0(A_388), u1_struct_0(B_389)) | ~v1_funct_1(D_387) | ~l1_pre_topc(B_389) | ~v2_pre_topc(B_389) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.60/3.50  tff(c_7132, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_111, c_7129])).
% 9.60/3.50  tff(c_7139, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_110, c_7132])).
% 9.60/3.50  tff(c_7140, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_6459, c_7139])).
% 9.60/3.50  tff(c_7271, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_7140])).
% 9.60/3.50  tff(c_7274, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_7271])).
% 9.60/3.50  tff(c_7278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_7274])).
% 9.60/3.50  tff(c_7280, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_7140])).
% 9.60/3.50  tff(c_6935, plain, (![B_356, A_357]: (m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(A_357))) | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_357), u1_pre_topc(A_357))))) | ~v3_pre_topc(B_356, g1_pre_topc(u1_struct_0(A_357), u1_pre_topc(A_357))) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.60/3.50  tff(c_6976, plain, (![A_359, A_360]: (m1_subset_1(A_359, k1_zfmisc_1(u1_struct_0(A_360))) | ~v3_pre_topc(A_359, g1_pre_topc(u1_struct_0(A_360), u1_pre_topc(A_360))) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | ~r1_tarski(A_359, u1_struct_0(g1_pre_topc(u1_struct_0(A_360), u1_pre_topc(A_360)))))), inference(resolution, [status(thm)], [c_10, c_6935])).
% 9.60/3.50  tff(c_7042, plain, (![A_376]: (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_376), u1_pre_topc(A_376))), k1_zfmisc_1(u1_struct_0(A_376))) | ~v3_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(A_376), u1_pre_topc(A_376))), g1_pre_topc(u1_struct_0(A_376), u1_pre_topc(A_376))) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376))), inference(resolution, [status(thm)], [c_6, c_6976])).
% 9.60/3.50  tff(c_7052, plain, (![A_377]: (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_377), u1_pre_topc(A_377))), k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_377), u1_pre_topc(A_377))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_377), u1_pre_topc(A_377))))), inference(resolution, [status(thm)], [c_6477, c_7042])).
% 9.60/3.50  tff(c_7074, plain, (![A_377]: (r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_377), u1_pre_topc(A_377))), u1_struct_0(A_377)) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_377), u1_pre_topc(A_377))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_377), u1_pre_topc(A_377))))), inference(resolution, [status(thm)], [c_7052, c_8])).
% 9.60/3.50  tff(c_6631, plain, (![B_318, A_319]: (m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_319), u1_pre_topc(A_319))))) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_319))) | ~v3_pre_topc(B_318, A_319) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.60/3.50  tff(c_6656, plain, (![B_321, A_322]: (r1_tarski(B_321, u1_struct_0(g1_pre_topc(u1_struct_0(A_322), u1_pre_topc(A_322)))) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_322))) | ~v3_pre_topc(B_321, A_322) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322))), inference(resolution, [status(thm)], [c_6631, c_8])).
% 9.60/3.50  tff(c_7107, plain, (![A_384, B_385]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_384), u1_pre_topc(A_384)))=B_385 | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(A_384), u1_pre_topc(A_384))), B_385) | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0(A_384))) | ~v3_pre_topc(B_385, A_384) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384))), inference(resolution, [status(thm)], [c_6656, c_2])).
% 9.60/3.50  tff(c_7259, plain, (![A_401]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401)))=u1_struct_0(A_401) | ~m1_subset_1(u1_struct_0(A_401), k1_zfmisc_1(u1_struct_0(A_401))) | ~v3_pre_topc(u1_struct_0(A_401), A_401) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401))))), inference(resolution, [status(thm)], [c_7074, c_7107])).
% 9.60/3.50  tff(c_7266, plain, (![A_401]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401)))=u1_struct_0(A_401) | ~v3_pre_topc(u1_struct_0(A_401), A_401) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_401), u1_pre_topc(A_401))) | ~r1_tarski(u1_struct_0(A_401), u1_struct_0(A_401)))), inference(resolution, [status(thm)], [c_10, c_7259])).
% 9.60/3.50  tff(c_7281, plain, (![A_402]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_402), u1_pre_topc(A_402)))=u1_struct_0(A_402) | ~v3_pre_topc(u1_struct_0(A_402), A_402) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_402), u1_pre_topc(A_402))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_402), u1_pre_topc(A_402))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7266])).
% 9.60/3.50  tff(c_7284, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_struct_0('#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_7280, c_7281])).
% 9.60/3.50  tff(c_7290, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_struct_0('#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_7284])).
% 9.60/3.50  tff(c_7292, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_7290])).
% 9.60/3.50  tff(c_7295, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_179, c_7292])).
% 9.60/3.50  tff(c_7299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_7295])).
% 9.60/3.50  tff(c_7300, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4') | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_7290])).
% 9.60/3.50  tff(c_7315, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_7300])).
% 9.60/3.50  tff(c_7318, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6477, c_7315])).
% 9.60/3.50  tff(c_7322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_98, c_7318])).
% 9.60/3.50  tff(c_7323, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_7300])).
% 9.60/3.50  tff(c_7343, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_7323, c_111])).
% 9.60/3.50  tff(c_7344, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_7323, c_110])).
% 9.60/3.50  tff(c_7302, plain, (![D_403, A_404, B_405]: (v5_pre_topc(D_403, g1_pre_topc(u1_struct_0(A_404), u1_pre_topc(A_404)), B_405) | ~v5_pre_topc(D_403, A_404, B_405) | ~m1_subset_1(D_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_404), u1_pre_topc(A_404))), u1_struct_0(B_405)))) | ~v1_funct_2(D_403, u1_struct_0(g1_pre_topc(u1_struct_0(A_404), u1_pre_topc(A_404))), u1_struct_0(B_405)) | ~m1_subset_1(D_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404), u1_struct_0(B_405)))) | ~v1_funct_2(D_403, u1_struct_0(A_404), u1_struct_0(B_405)) | ~v1_funct_1(D_403) | ~l1_pre_topc(B_405) | ~v2_pre_topc(B_405) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.60/3.50  tff(c_7305, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_111, c_7302])).
% 9.60/3.50  tff(c_7312, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_90, c_110, c_7305])).
% 9.60/3.50  tff(c_7313, plain, (~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_6459, c_7312])).
% 9.60/3.50  tff(c_7325, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_7313])).
% 9.60/3.50  tff(c_7328, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_7325])).
% 9.60/3.50  tff(c_7332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_7328])).
% 9.60/3.50  tff(c_7333, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_7313])).
% 9.60/3.50  tff(c_7934, plain, (~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_7333])).
% 9.60/3.50  tff(c_6460, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_108])).
% 9.60/3.50  tff(c_76, plain, (![D_58, A_44, B_52]: (v5_pre_topc(D_58, A_44, g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52))) | ~v5_pre_topc(D_58, A_44, B_52) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44), u1_struct_0(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52)))))) | ~v1_funct_2(D_58, u1_struct_0(A_44), u1_struct_0(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52)))) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44), u1_struct_0(B_52)))) | ~v1_funct_2(D_58, u1_struct_0(A_44), u1_struct_0(B_52)) | ~v1_funct_1(D_58) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.60/3.50  tff(c_8017, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_7343, c_76])).
% 9.60/3.50  tff(c_8026, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_92, c_90, c_88, c_86, c_7344, c_6460, c_8017])).
% 9.60/3.50  tff(c_8028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7934, c_8026])).
% 9.60/3.50  tff(c_8029, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_7333])).
% 9.60/3.50  tff(c_8096, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_8029])).
% 9.60/3.50  tff(c_8099, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_179, c_8096])).
% 9.60/3.50  tff(c_8103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_8099])).
% 9.60/3.50  tff(c_8104, plain, (~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(splitRight, [status(thm)], [c_8029])).
% 9.60/3.50  tff(c_8136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7343, c_7344, c_8104])).
% 9.60/3.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.60/3.50  
% 9.60/3.50  Inference rules
% 9.60/3.50  ----------------------
% 9.60/3.50  #Ref     : 0
% 9.60/3.50  #Sup     : 1618
% 9.60/3.50  #Fact    : 0
% 9.60/3.50  #Define  : 0
% 9.60/3.50  #Split   : 17
% 9.60/3.50  #Chain   : 0
% 9.60/3.50  #Close   : 0
% 9.60/3.50  
% 9.60/3.50  Ordering : KBO
% 9.60/3.50  
% 9.60/3.50  Simplification rules
% 9.60/3.50  ----------------------
% 9.60/3.50  #Subsume      : 245
% 9.60/3.50  #Demod        : 4909
% 9.60/3.50  #Tautology    : 641
% 9.60/3.50  #SimpNegUnit  : 11
% 9.60/3.50  #BackRed      : 12
% 9.60/3.50  
% 9.60/3.50  #Partial instantiations: 0
% 9.60/3.50  #Strategies tried      : 1
% 9.60/3.50  
% 9.60/3.50  Timing (in seconds)
% 9.60/3.50  ----------------------
% 9.60/3.51  Preprocessing        : 0.39
% 9.60/3.51  Parsing              : 0.20
% 9.60/3.51  CNF conversion       : 0.03
% 9.60/3.51  Main loop            : 2.32
% 9.60/3.51  Inferencing          : 0.71
% 9.60/3.51  Reduction            : 1.00
% 9.60/3.51  Demodulation         : 0.80
% 9.60/3.51  BG Simplification    : 0.08
% 9.60/3.51  Subsumption          : 0.43
% 9.60/3.51  Abstraction          : 0.10
% 9.60/3.51  MUC search           : 0.00
% 9.60/3.51  Cooper               : 0.00
% 9.60/3.51  Total                : 2.77
% 9.60/3.51  Index Insertion      : 0.00
% 9.60/3.51  Index Deletion       : 0.00
% 9.60/3.51  Index Matching       : 0.00
% 9.60/3.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
