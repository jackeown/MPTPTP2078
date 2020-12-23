%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 289 expanded)
%              Number of leaves         :   41 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  297 (1767 expanded)
%              Number of equality atoms :    7 (  93 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_237,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_36,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_93,plain,(
    ! [B_283,A_284] :
      ( l1_pre_topc(B_283)
      | ~ m1_pre_topc(B_283,A_284)
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_99,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_96])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [B_301,A_302] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_308,A_309,B_310] :
      ( m1_subset_1(A_308,u1_struct_0(A_309))
      | ~ r2_hidden(A_308,u1_struct_0(B_310))
      | ~ m1_pre_topc(B_310,A_309)
      | ~ l1_pre_topc(A_309) ) ),
    inference(resolution,[status(thm)],[c_136,c_12])).

tff(c_182,plain,(
    ! [A_316,A_317,B_318] :
      ( m1_subset_1(A_316,u1_struct_0(A_317))
      | ~ m1_pre_topc(B_318,A_317)
      | ~ l1_pre_topc(A_317)
      | v1_xboole_0(u1_struct_0(B_318))
      | ~ m1_subset_1(A_316,u1_struct_0(B_318)) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_184,plain,(
    ! [A_316] :
      ( m1_subset_1(A_316,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_316,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_182])).

tff(c_187,plain,(
    ! [A_316] :
      ( m1_subset_1(A_316,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_316,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_184])).

tff(c_188,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_18,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_191,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_188,c_18])).

tff(c_194,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_191])).

tff(c_211,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_194])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_211])).

tff(c_217,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_44,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_28,plain,(
    ! [B_31,A_29] :
      ( m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_256,plain,(
    ! [B_328,A_329] :
      ( v3_pre_topc(u1_struct_0(B_328),A_329)
      | ~ v1_tsep_1(B_328,A_329)
      | ~ m1_subset_1(u1_struct_0(B_328),k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ m1_pre_topc(B_328,A_329)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_267,plain,(
    ! [B_31,A_29] :
      ( v3_pre_topc(u1_struct_0(B_31),A_29)
      | ~ v1_tsep_1(B_31,A_29)
      | ~ v2_pre_topc(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_28,c_256])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_101,plain,(
    ! [A_287,B_288] :
      ( r1_tarski(A_287,B_288)
      | ~ m1_subset_1(A_287,k1_zfmisc_1(B_288)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_76,c_101])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_75,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_66])).

tff(c_156,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_73,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_162,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_73])).

tff(c_318,plain,(
    ! [E_356,D_357,B_355,G_353,A_354,C_352] :
      ( r1_tmap_1(B_355,A_354,C_352,G_353)
      | ~ r1_tmap_1(D_357,A_354,k2_tmap_1(B_355,A_354,C_352,D_357),G_353)
      | ~ r1_tarski(E_356,u1_struct_0(D_357))
      | ~ r2_hidden(G_353,E_356)
      | ~ v3_pre_topc(E_356,B_355)
      | ~ m1_subset_1(G_353,u1_struct_0(D_357))
      | ~ m1_subset_1(G_353,u1_struct_0(B_355))
      | ~ m1_subset_1(E_356,k1_zfmisc_1(u1_struct_0(B_355)))
      | ~ m1_pre_topc(D_357,B_355)
      | v2_struct_0(D_357)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_355),u1_struct_0(A_354))))
      | ~ v1_funct_2(C_352,u1_struct_0(B_355),u1_struct_0(A_354))
      | ~ v1_funct_1(C_352)
      | ~ l1_pre_topc(B_355)
      | ~ v2_pre_topc(B_355)
      | v2_struct_0(B_355)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_322,plain,(
    ! [E_356] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_356,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_356)
      | ~ v3_pre_topc(E_356,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_356,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_162,c_318])).

tff(c_329,plain,(
    ! [E_356] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_356,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_356)
      | ~ v3_pre_topc(E_356,'#skF_2')
      | ~ m1_subset_1(E_356,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_48,c_42,c_74,c_38,c_322])).

tff(c_331,plain,(
    ! [E_358] :
      ( ~ r1_tarski(E_358,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_358)
      | ~ v3_pre_topc(E_358,'#skF_2')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_46,c_156,c_329])).

tff(c_335,plain,(
    ! [B_31] :
      ( ~ r1_tarski(u1_struct_0(B_31),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_31))
      | ~ v3_pre_topc(u1_struct_0(B_31),'#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_331])).

tff(c_370,plain,(
    ! [B_360] :
      ( ~ r1_tarski(u1_struct_0(B_360),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_360))
      | ~ v3_pre_topc(u1_struct_0(B_360),'#skF_2')
      | ~ m1_pre_topc(B_360,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_335])).

tff(c_378,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_113,c_370])).

tff(c_384,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_378])).

tff(c_385,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_388,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_267,c_385])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_56,c_44,c_388])).

tff(c_393,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_403,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_393])).

tff(c_406,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_403])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_406])).

tff(c_410,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_541,plain,(
    ! [A_391,D_393,B_392,C_390,F_394] :
      ( r1_tmap_1(D_393,A_391,k2_tmap_1(B_392,A_391,C_390,D_393),F_394)
      | ~ r1_tmap_1(B_392,A_391,C_390,F_394)
      | ~ m1_subset_1(F_394,u1_struct_0(D_393))
      | ~ m1_subset_1(F_394,u1_struct_0(B_392))
      | ~ m1_pre_topc(D_393,B_392)
      | v2_struct_0(D_393)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_392),u1_struct_0(A_391))))
      | ~ v1_funct_2(C_390,u1_struct_0(B_392),u1_struct_0(A_391))
      | ~ v1_funct_1(C_390)
      | ~ l1_pre_topc(B_392)
      | ~ v2_pre_topc(B_392)
      | v2_struct_0(B_392)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_546,plain,(
    ! [D_393,F_394] :
      ( r1_tmap_1(D_393,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_393),F_394)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_394)
      | ~ m1_subset_1(F_394,u1_struct_0(D_393))
      | ~ m1_subset_1(F_394,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_393,'#skF_2')
      | v2_struct_0(D_393)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_541])).

tff(c_553,plain,(
    ! [D_393,F_394] :
      ( r1_tmap_1(D_393,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_393),F_394)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_394)
      | ~ m1_subset_1(F_394,u1_struct_0(D_393))
      | ~ m1_subset_1(F_394,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_393,'#skF_2')
      | v2_struct_0(D_393)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_546])).

tff(c_557,plain,(
    ! [D_401,F_402] :
      ( r1_tmap_1(D_401,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_401),F_402)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_402)
      | ~ m1_subset_1(F_402,u1_struct_0(D_401))
      | ~ m1_subset_1(F_402,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_401,'#skF_2')
      | v2_struct_0(D_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_553])).

tff(c_409,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_562,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_557,c_409])).

tff(c_569,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_38,c_410,c_562])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.46  
% 2.94/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.46  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.34/1.46  
% 3.34/1.46  %Foreground sorts:
% 3.34/1.46  
% 3.34/1.46  
% 3.34/1.46  %Background operators:
% 3.34/1.46  
% 3.34/1.46  
% 3.34/1.46  %Foreground operators:
% 3.34/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.34/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.34/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.46  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.34/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.34/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.34/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.46  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.34/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.34/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.34/1.46  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.34/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.34/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.34/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.46  
% 3.34/1.48  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.34/1.48  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.34/1.48  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.34/1.48  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.34/1.49  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.34/1.49  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.34/1.49  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.34/1.49  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.34/1.49  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.34/1.49  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.34/1.49  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.34/1.49  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.34/1.49  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.34/1.49  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_36, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_74, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 3.34/1.49  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_93, plain, (![B_283, A_284]: (l1_pre_topc(B_283) | ~m1_pre_topc(B_283, A_284) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.34/1.49  tff(c_96, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_93])).
% 3.34/1.49  tff(c_99, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_96])).
% 3.34/1.49  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.34/1.49  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.49  tff(c_136, plain, (![B_301, A_302]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(u1_struct_0(A_302))) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.49  tff(c_12, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.49  tff(c_157, plain, (![A_308, A_309, B_310]: (m1_subset_1(A_308, u1_struct_0(A_309)) | ~r2_hidden(A_308, u1_struct_0(B_310)) | ~m1_pre_topc(B_310, A_309) | ~l1_pre_topc(A_309))), inference(resolution, [status(thm)], [c_136, c_12])).
% 3.34/1.49  tff(c_182, plain, (![A_316, A_317, B_318]: (m1_subset_1(A_316, u1_struct_0(A_317)) | ~m1_pre_topc(B_318, A_317) | ~l1_pre_topc(A_317) | v1_xboole_0(u1_struct_0(B_318)) | ~m1_subset_1(A_316, u1_struct_0(B_318)))), inference(resolution, [status(thm)], [c_6, c_157])).
% 3.34/1.49  tff(c_184, plain, (![A_316]: (m1_subset_1(A_316, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_316, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_182])).
% 3.34/1.49  tff(c_187, plain, (![A_316]: (m1_subset_1(A_316, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_316, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_184])).
% 3.34/1.49  tff(c_188, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_187])).
% 3.34/1.49  tff(c_18, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.49  tff(c_191, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_188, c_18])).
% 3.34/1.49  tff(c_194, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_191])).
% 3.34/1.49  tff(c_211, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_194])).
% 3.34/1.49  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_211])).
% 3.34/1.49  tff(c_217, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_187])).
% 3.34/1.49  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_44, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_28, plain, (![B_31, A_29]: (m1_subset_1(u1_struct_0(B_31), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.49  tff(c_256, plain, (![B_328, A_329]: (v3_pre_topc(u1_struct_0(B_328), A_329) | ~v1_tsep_1(B_328, A_329) | ~m1_subset_1(u1_struct_0(B_328), k1_zfmisc_1(u1_struct_0(A_329))) | ~m1_pre_topc(B_328, A_329) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.49  tff(c_267, plain, (![B_31, A_29]: (v3_pre_topc(u1_struct_0(B_31), A_29) | ~v1_tsep_1(B_31, A_29) | ~v2_pre_topc(A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_28, c_256])).
% 3.34/1.49  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.49  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.49  tff(c_76, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.34/1.49  tff(c_101, plain, (![A_287, B_288]: (r1_tarski(A_287, B_288) | ~m1_subset_1(A_287, k1_zfmisc_1(B_288)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.49  tff(c_113, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_76, c_101])).
% 3.34/1.49  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_66, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_75, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_66])).
% 3.34/1.49  tff(c_156, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_75])).
% 3.34/1.49  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_72, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.34/1.49  tff(c_73, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72])).
% 3.34/1.49  tff(c_162, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_156, c_73])).
% 3.34/1.49  tff(c_318, plain, (![E_356, D_357, B_355, G_353, A_354, C_352]: (r1_tmap_1(B_355, A_354, C_352, G_353) | ~r1_tmap_1(D_357, A_354, k2_tmap_1(B_355, A_354, C_352, D_357), G_353) | ~r1_tarski(E_356, u1_struct_0(D_357)) | ~r2_hidden(G_353, E_356) | ~v3_pre_topc(E_356, B_355) | ~m1_subset_1(G_353, u1_struct_0(D_357)) | ~m1_subset_1(G_353, u1_struct_0(B_355)) | ~m1_subset_1(E_356, k1_zfmisc_1(u1_struct_0(B_355))) | ~m1_pre_topc(D_357, B_355) | v2_struct_0(D_357) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_355), u1_struct_0(A_354)))) | ~v1_funct_2(C_352, u1_struct_0(B_355), u1_struct_0(A_354)) | ~v1_funct_1(C_352) | ~l1_pre_topc(B_355) | ~v2_pre_topc(B_355) | v2_struct_0(B_355) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.34/1.49  tff(c_322, plain, (![E_356]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_356, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_356) | ~v3_pre_topc(E_356, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_356, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_162, c_318])).
% 3.34/1.49  tff(c_329, plain, (![E_356]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_356, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_356) | ~v3_pre_topc(E_356, '#skF_2') | ~m1_subset_1(E_356, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_48, c_42, c_74, c_38, c_322])).
% 3.34/1.49  tff(c_331, plain, (![E_358]: (~r1_tarski(E_358, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_358) | ~v3_pre_topc(E_358, '#skF_2') | ~m1_subset_1(E_358, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_46, c_156, c_329])).
% 3.34/1.49  tff(c_335, plain, (![B_31]: (~r1_tarski(u1_struct_0(B_31), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_31)) | ~v3_pre_topc(u1_struct_0(B_31), '#skF_2') | ~m1_pre_topc(B_31, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_331])).
% 3.34/1.49  tff(c_370, plain, (![B_360]: (~r1_tarski(u1_struct_0(B_360), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_360)) | ~v3_pre_topc(u1_struct_0(B_360), '#skF_2') | ~m1_pre_topc(B_360, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_335])).
% 3.34/1.49  tff(c_378, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_113, c_370])).
% 3.34/1.49  tff(c_384, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_378])).
% 3.34/1.49  tff(c_385, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_384])).
% 3.34/1.49  tff(c_388, plain, (~v1_tsep_1('#skF_4', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_267, c_385])).
% 3.34/1.49  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_56, c_44, c_388])).
% 3.34/1.49  tff(c_393, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_384])).
% 3.34/1.49  tff(c_403, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_393])).
% 3.34/1.49  tff(c_406, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_403])).
% 3.34/1.49  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_406])).
% 3.34/1.49  tff(c_410, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.34/1.49  tff(c_541, plain, (![A_391, D_393, B_392, C_390, F_394]: (r1_tmap_1(D_393, A_391, k2_tmap_1(B_392, A_391, C_390, D_393), F_394) | ~r1_tmap_1(B_392, A_391, C_390, F_394) | ~m1_subset_1(F_394, u1_struct_0(D_393)) | ~m1_subset_1(F_394, u1_struct_0(B_392)) | ~m1_pre_topc(D_393, B_392) | v2_struct_0(D_393) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_392), u1_struct_0(A_391)))) | ~v1_funct_2(C_390, u1_struct_0(B_392), u1_struct_0(A_391)) | ~v1_funct_1(C_390) | ~l1_pre_topc(B_392) | ~v2_pre_topc(B_392) | v2_struct_0(B_392) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.34/1.49  tff(c_546, plain, (![D_393, F_394]: (r1_tmap_1(D_393, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_393), F_394) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_394) | ~m1_subset_1(F_394, u1_struct_0(D_393)) | ~m1_subset_1(F_394, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_393, '#skF_2') | v2_struct_0(D_393) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_541])).
% 3.34/1.49  tff(c_553, plain, (![D_393, F_394]: (r1_tmap_1(D_393, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_393), F_394) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_394) | ~m1_subset_1(F_394, u1_struct_0(D_393)) | ~m1_subset_1(F_394, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_393, '#skF_2') | v2_struct_0(D_393) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_546])).
% 3.34/1.49  tff(c_557, plain, (![D_401, F_402]: (r1_tmap_1(D_401, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_401), F_402) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_402) | ~m1_subset_1(F_402, u1_struct_0(D_401)) | ~m1_subset_1(F_402, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_401, '#skF_2') | v2_struct_0(D_401))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_553])).
% 3.34/1.49  tff(c_409, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.34/1.49  tff(c_562, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_557, c_409])).
% 3.34/1.49  tff(c_569, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_38, c_410, c_562])).
% 3.34/1.49  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_569])).
% 3.34/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.49  
% 3.34/1.49  Inference rules
% 3.34/1.49  ----------------------
% 3.34/1.49  #Ref     : 0
% 3.34/1.49  #Sup     : 88
% 3.34/1.49  #Fact    : 0
% 3.34/1.49  #Define  : 0
% 3.34/1.49  #Split   : 7
% 3.34/1.49  #Chain   : 0
% 3.34/1.49  #Close   : 0
% 3.34/1.49  
% 3.34/1.49  Ordering : KBO
% 3.34/1.49  
% 3.34/1.49  Simplification rules
% 3.34/1.49  ----------------------
% 3.34/1.49  #Subsume      : 24
% 3.34/1.49  #Demod        : 87
% 3.34/1.49  #Tautology    : 20
% 3.34/1.49  #SimpNegUnit  : 27
% 3.34/1.49  #BackRed      : 0
% 3.34/1.49  
% 3.34/1.49  #Partial instantiations: 0
% 3.34/1.49  #Strategies tried      : 1
% 3.34/1.49  
% 3.34/1.49  Timing (in seconds)
% 3.34/1.49  ----------------------
% 3.46/1.49  Preprocessing        : 0.39
% 3.46/1.49  Parsing              : 0.20
% 3.46/1.49  CNF conversion       : 0.05
% 3.46/1.49  Main loop            : 0.34
% 3.46/1.49  Inferencing          : 0.12
% 3.46/1.49  Reduction            : 0.11
% 3.46/1.49  Demodulation         : 0.08
% 3.46/1.49  BG Simplification    : 0.02
% 3.46/1.49  Subsumption          : 0.07
% 3.46/1.49  Abstraction          : 0.01
% 3.46/1.49  MUC search           : 0.00
% 3.46/1.49  Cooper               : 0.00
% 3.46/1.49  Total                : 0.77
% 3.46/1.49  Index Insertion      : 0.00
% 3.46/1.49  Index Deletion       : 0.00
% 3.46/1.49  Index Matching       : 0.00
% 3.46/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
