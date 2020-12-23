%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1745+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:20 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 190 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  217 (1468 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
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
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ( ( r1_tmap_1(C,A,D,F)
                                & v5_pre_topc(E,A,B) )
                             => r1_tmap_1(C,B,k1_partfun1(u1_struct_0(C),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),D,E),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_78,axiom,(
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
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_129,axiom,(
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
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(C))
                             => ( ( G = k3_funct_2(u1_struct_0(B),u1_struct_0(C),D,F)
                                  & r1_tmap_1(B,C,D,F)
                                  & r1_tmap_1(C,A,E,G) )
                               => r1_tmap_1(B,A,k1_partfun1(u1_struct_0(B),u1_struct_0(C),u1_struct_0(C),u1_struct_0(A),D,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_26,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_18,plain,(
    v5_pre_topc('#skF_6','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_36,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_55,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( m1_subset_1(k3_funct_2(A_215,B_216,C_217,D_218),B_216)
      | ~ m1_subset_1(D_218,A_215)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_2(C_217,A_215,B_216)
      | ~ v1_funct_1(C_217)
      | v1_xboole_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57,plain,(
    ! [D_218] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_218),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_62,plain,(
    ! [D_218] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_218),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_57])).

tff(c_66,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_6])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_69])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_75])).

tff(c_80,plain,(
    ! [D_218] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_218),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_115,plain,(
    ! [B_227,A_228,C_229,D_230] :
      ( r1_tmap_1(B_227,A_228,C_229,D_230)
      | ~ m1_subset_1(D_230,u1_struct_0(B_227))
      | ~ v5_pre_topc(C_229,B_227,A_228)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_227),u1_struct_0(A_228))))
      | ~ v1_funct_2(C_229,u1_struct_0(B_227),u1_struct_0(A_228))
      | ~ v1_funct_1(C_229)
      | ~ l1_pre_topc(B_227)
      | ~ v2_pre_topc(B_227)
      | v2_struct_0(B_227)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_117,plain,(
    ! [A_228,C_229,D_218] :
      ( r1_tmap_1('#skF_2',A_228,C_229,k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_218))
      | ~ v5_pre_topc(C_229,'#skF_2',A_228)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_228))))
      | ~ v1_funct_2(C_229,u1_struct_0('#skF_2'),u1_struct_0(A_228))
      | ~ v1_funct_1(C_229)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228)
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_80,c_115])).

tff(c_124,plain,(
    ! [A_228,C_229,D_218] :
      ( r1_tmap_1('#skF_2',A_228,C_229,k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_218))
      | ~ v5_pre_topc(C_229,'#skF_2',A_228)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_228))))
      | ~ v1_funct_2(C_229,u1_struct_0('#skF_2'),u1_struct_0(A_228))
      | ~ v1_funct_1(C_229)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228)
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_117])).

tff(c_142,plain,(
    ! [A_233,C_234,D_235] :
      ( r1_tmap_1('#skF_2',A_233,C_234,k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_235))
      | ~ v5_pre_topc(C_234,'#skF_2',A_233)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_233))))
      | ~ v1_funct_2(C_234,u1_struct_0('#skF_2'),u1_struct_0(A_233))
      | ~ v1_funct_1(C_234)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233)
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_124])).

tff(c_144,plain,(
    ! [D_235] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_235))
      | ~ v5_pre_topc('#skF_6','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_142])).

tff(c_147,plain,(
    ! [D_235] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_235))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_28,c_26,c_18,c_144])).

tff(c_148,plain,(
    ! [D_235] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_235))
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_147])).

tff(c_38,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_20,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_151,plain,(
    ! [E_244,D_242,B_245,A_243,F_241,C_240] :
      ( r1_tmap_1(B_245,A_243,k1_partfun1(u1_struct_0(B_245),u1_struct_0(C_240),u1_struct_0(C_240),u1_struct_0(A_243),D_242,E_244),F_241)
      | ~ r1_tmap_1(C_240,A_243,E_244,k3_funct_2(u1_struct_0(B_245),u1_struct_0(C_240),D_242,F_241))
      | ~ r1_tmap_1(B_245,C_240,D_242,F_241)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_245),u1_struct_0(C_240),D_242,F_241),u1_struct_0(C_240))
      | ~ m1_subset_1(F_241,u1_struct_0(B_245))
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240),u1_struct_0(A_243))))
      | ~ v1_funct_2(E_244,u1_struct_0(C_240),u1_struct_0(A_243))
      | ~ v1_funct_1(E_244)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_245),u1_struct_0(C_240))))
      | ~ v1_funct_2(D_242,u1_struct_0(B_245),u1_struct_0(C_240))
      | ~ v1_funct_1(D_242)
      | ~ l1_pre_topc(C_240)
      | ~ v2_pre_topc(C_240)
      | v2_struct_0(C_240)
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_16,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k1_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_157,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'))
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_151,c_16])).

tff(c_161,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_36,c_50,c_48,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_157])).

tff(c_162,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_52,c_161])).

tff(c_163,plain,(
    ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_166,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_163])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_166])).

tff(c_171,plain,(
    ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_181,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_148,c_171])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_181])).

%------------------------------------------------------------------------------
