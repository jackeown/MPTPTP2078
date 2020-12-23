%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:49 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 209 expanded)
%              Number of leaves         :   35 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  248 (1585 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_193,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tmap_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_95,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_146,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_52,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_36,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_34,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_26,plain,(
    v5_pre_topc('#skF_8','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_46,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_44,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_42,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_40,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_89,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( m1_subset_1(k3_funct_2(A_232,B_233,C_234,D_235),B_233)
      | ~ m1_subset_1(D_235,A_232)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_2(C_234,A_232,B_233)
      | ~ v1_funct_1(C_234)
      | v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [D_235] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_235),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_96,plain,(
    ! [D_235] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_235),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_6'))
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_91])).

tff(c_100,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_228] :
      ( m1_subset_1('#skF_2'(A_228),k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_229,A_230] :
      ( ~ v1_xboole_0(u1_struct_0(A_229))
      | ~ r2_hidden(A_230,'#skF_2'(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_78,c_6])).

tff(c_87,plain,(
    ! [A_229] :
      ( ~ v1_xboole_0(u1_struct_0(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229)
      | v1_xboole_0('#skF_2'(A_229)) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_103,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_100,c_87])).

tff(c_106,plain,
    ( v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_103])).

tff(c_107,plain,(
    v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_106])).

tff(c_12,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_2'(A_12))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_107,c_12])).

tff(c_113,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_113])).

tff(c_116,plain,(
    ! [D_235] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_235),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_153,plain,(
    ! [B_244,A_245,C_246,D_247] :
      ( r1_tmap_1(B_244,A_245,C_246,D_247)
      | ~ m1_subset_1(D_247,u1_struct_0(B_244))
      | ~ v5_pre_topc(C_246,B_244,A_245)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_244),u1_struct_0(A_245))))
      | ~ v1_funct_2(C_246,u1_struct_0(B_244),u1_struct_0(A_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_pre_topc(B_244)
      | ~ v2_pre_topc(B_244)
      | v2_struct_0(B_244)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_155,plain,(
    ! [A_245,C_246,D_235] :
      ( r1_tmap_1('#skF_4',A_245,C_246,k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_235))
      | ~ v5_pre_topc(C_246,'#skF_4',A_245)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_245))))
      | ~ v1_funct_2(C_246,u1_struct_0('#skF_4'),u1_struct_0(A_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245)
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_116,c_153])).

tff(c_162,plain,(
    ! [A_245,C_246,D_235] :
      ( r1_tmap_1('#skF_4',A_245,C_246,k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_235))
      | ~ v5_pre_topc(C_246,'#skF_4',A_245)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_245))))
      | ~ v1_funct_2(C_246,u1_struct_0('#skF_4'),u1_struct_0(A_245))
      | ~ v1_funct_1(C_246)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245)
      | ~ m1_subset_1(D_235,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_155])).

tff(c_180,plain,(
    ! [A_250,C_251,D_252] :
      ( r1_tmap_1('#skF_4',A_250,C_251,k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_252))
      | ~ v5_pre_topc(C_251,'#skF_4',A_250)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_250))))
      | ~ v1_funct_2(C_251,u1_struct_0('#skF_4'),u1_struct_0(A_250))
      | ~ v1_funct_1(C_251)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250)
      | ~ m1_subset_1(D_252,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_162])).

tff(c_182,plain,(
    ! [D_252] :
      ( r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_252))
      | ~ v5_pre_topc('#skF_8','#skF_4','#skF_5')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_252,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_32,c_180])).

tff(c_185,plain,(
    ! [D_252] :
      ( r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_252))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_252,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_34,c_26,c_182])).

tff(c_186,plain,(
    ! [D_252] :
      ( r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_252))
      | ~ m1_subset_1(D_252,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_185])).

tff(c_28,plain,(
    r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_189,plain,(
    ! [B_259,A_260,F_262,C_257,E_261,D_258] :
      ( r1_tmap_1(B_259,A_260,k1_partfun1(u1_struct_0(B_259),u1_struct_0(C_257),u1_struct_0(C_257),u1_struct_0(A_260),D_258,E_261),F_262)
      | ~ r1_tmap_1(C_257,A_260,E_261,k3_funct_2(u1_struct_0(B_259),u1_struct_0(C_257),D_258,F_262))
      | ~ r1_tmap_1(B_259,C_257,D_258,F_262)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_259),u1_struct_0(C_257),D_258,F_262),u1_struct_0(C_257))
      | ~ m1_subset_1(F_262,u1_struct_0(B_259))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0(A_260))))
      | ~ v1_funct_2(E_261,u1_struct_0(C_257),u1_struct_0(A_260))
      | ~ v1_funct_1(E_261)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_259),u1_struct_0(C_257))))
      | ~ v1_funct_2(D_258,u1_struct_0(B_259),u1_struct_0(C_257))
      | ~ v1_funct_1(D_258)
      | ~ l1_pre_topc(C_257)
      | ~ v2_pre_topc(C_257)
      | v2_struct_0(C_257)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_24,plain,(
    ~ r1_tmap_1('#skF_6','#skF_5',k1_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_195,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'))
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9')
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_189,c_24])).

tff(c_199,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_58,c_56,c_42,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_195])).

tff(c_200,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_60,c_199])).

tff(c_201,plain,(
    ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_204,plain,(
    ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_116,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_204])).

tff(c_209,plain,(
    ~ r1_tmap_1('#skF_4','#skF_5','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_219,plain,(
    ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_186,c_209])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.92  
% 3.99/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.92  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 3.99/1.92  
% 3.99/1.92  %Foreground sorts:
% 3.99/1.92  
% 3.99/1.92  
% 3.99/1.92  %Background operators:
% 3.99/1.92  
% 3.99/1.92  
% 3.99/1.92  %Foreground operators:
% 3.99/1.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.99/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.99/1.92  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.99/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.99/1.92  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.99/1.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.99/1.92  tff('#skF_7', type, '#skF_7': $i).
% 3.99/1.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.92  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.99/1.92  tff('#skF_6', type, '#skF_6': $i).
% 3.99/1.92  tff('#skF_9', type, '#skF_9': $i).
% 3.99/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.92  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.99/1.92  tff('#skF_8', type, '#skF_8': $i).
% 3.99/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.99/1.92  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.92  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.99/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.92  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.99/1.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.99/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.99/1.92  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.99/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.92  
% 3.99/1.96  tff(f_193, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => ((r1_tmap_1(C, A, D, F) & v5_pre_topc(E, A, B)) => r1_tmap_1(C, B, k1_partfun1(u1_struct_0(C), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), D, E), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tmap_1)).
% 3.99/1.96  tff(f_51, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 3.99/1.96  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.99/1.96  tff(f_66, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.99/1.96  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.99/1.96  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 3.99/1.96  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 3.99/1.96  tff(c_30, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_52, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_50, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_36, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_34, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_26, plain, (v5_pre_topc('#skF_8', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_46, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_44, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_42, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_40, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_89, plain, (![A_232, B_233, C_234, D_235]: (m1_subset_1(k3_funct_2(A_232, B_233, C_234, D_235), B_233) | ~m1_subset_1(D_235, A_232) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_2(C_234, A_232, B_233) | ~v1_funct_1(C_234) | v1_xboole_0(A_232))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.99/1.96  tff(c_91, plain, (![D_235]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_235), u1_struct_0('#skF_4')) | ~m1_subset_1(D_235, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_38, c_89])).
% 3.99/1.96  tff(c_96, plain, (![D_235]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_235), u1_struct_0('#skF_4')) | ~m1_subset_1(D_235, u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_91])).
% 3.99/1.96  tff(c_100, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_96])).
% 3.99/1.96  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.96  tff(c_78, plain, (![A_228]: (m1_subset_1('#skF_2'(A_228), k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.99/1.96  tff(c_6, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.99/1.96  tff(c_82, plain, (![A_229, A_230]: (~v1_xboole_0(u1_struct_0(A_229)) | ~r2_hidden(A_230, '#skF_2'(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_78, c_6])).
% 3.99/1.96  tff(c_87, plain, (![A_229]: (~v1_xboole_0(u1_struct_0(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229) | v1_xboole_0('#skF_2'(A_229)))), inference(resolution, [status(thm)], [c_4, c_82])).
% 3.99/1.96  tff(c_103, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(resolution, [status(thm)], [c_100, c_87])).
% 3.99/1.96  tff(c_106, plain, (v2_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_103])).
% 3.99/1.96  tff(c_107, plain, (v1_xboole_0('#skF_2'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_106])).
% 3.99/1.96  tff(c_12, plain, (![A_12]: (~v1_xboole_0('#skF_2'(A_12)) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.99/1.96  tff(c_110, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_107, c_12])).
% 3.99/1.96  tff(c_113, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_110])).
% 3.99/1.96  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_113])).
% 3.99/1.96  tff(c_116, plain, (![D_235]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_235), u1_struct_0('#skF_4')) | ~m1_subset_1(D_235, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_96])).
% 3.99/1.96  tff(c_153, plain, (![B_244, A_245, C_246, D_247]: (r1_tmap_1(B_244, A_245, C_246, D_247) | ~m1_subset_1(D_247, u1_struct_0(B_244)) | ~v5_pre_topc(C_246, B_244, A_245) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_244), u1_struct_0(A_245)))) | ~v1_funct_2(C_246, u1_struct_0(B_244), u1_struct_0(A_245)) | ~v1_funct_1(C_246) | ~l1_pre_topc(B_244) | ~v2_pre_topc(B_244) | v2_struct_0(B_244) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.99/1.96  tff(c_155, plain, (![A_245, C_246, D_235]: (r1_tmap_1('#skF_4', A_245, C_246, k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_235)) | ~v5_pre_topc(C_246, '#skF_4', A_245) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_245)))) | ~v1_funct_2(C_246, u1_struct_0('#skF_4'), u1_struct_0(A_245)) | ~v1_funct_1(C_246) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245) | ~m1_subset_1(D_235, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_116, c_153])).
% 3.99/1.96  tff(c_162, plain, (![A_245, C_246, D_235]: (r1_tmap_1('#skF_4', A_245, C_246, k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_235)) | ~v5_pre_topc(C_246, '#skF_4', A_245) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_245)))) | ~v1_funct_2(C_246, u1_struct_0('#skF_4'), u1_struct_0(A_245)) | ~v1_funct_1(C_246) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245) | ~m1_subset_1(D_235, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_155])).
% 3.99/1.96  tff(c_180, plain, (![A_250, C_251, D_252]: (r1_tmap_1('#skF_4', A_250, C_251, k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_252)) | ~v5_pre_topc(C_251, '#skF_4', A_250) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_250)))) | ~v1_funct_2(C_251, u1_struct_0('#skF_4'), u1_struct_0(A_250)) | ~v1_funct_1(C_251) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250) | ~m1_subset_1(D_252, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_60, c_162])).
% 3.99/1.96  tff(c_182, plain, (![D_252]: (r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_252)) | ~v5_pre_topc('#skF_8', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(D_252, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_32, c_180])).
% 3.99/1.96  tff(c_185, plain, (![D_252]: (r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_252)) | v2_struct_0('#skF_5') | ~m1_subset_1(D_252, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_34, c_26, c_182])).
% 3.99/1.96  tff(c_186, plain, (![D_252]: (r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', D_252)) | ~m1_subset_1(D_252, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_54, c_185])).
% 3.99/1.96  tff(c_28, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_189, plain, (![B_259, A_260, F_262, C_257, E_261, D_258]: (r1_tmap_1(B_259, A_260, k1_partfun1(u1_struct_0(B_259), u1_struct_0(C_257), u1_struct_0(C_257), u1_struct_0(A_260), D_258, E_261), F_262) | ~r1_tmap_1(C_257, A_260, E_261, k3_funct_2(u1_struct_0(B_259), u1_struct_0(C_257), D_258, F_262)) | ~r1_tmap_1(B_259, C_257, D_258, F_262) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_259), u1_struct_0(C_257), D_258, F_262), u1_struct_0(C_257)) | ~m1_subset_1(F_262, u1_struct_0(B_259)) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0(A_260)))) | ~v1_funct_2(E_261, u1_struct_0(C_257), u1_struct_0(A_260)) | ~v1_funct_1(E_261) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_259), u1_struct_0(C_257)))) | ~v1_funct_2(D_258, u1_struct_0(B_259), u1_struct_0(C_257)) | ~v1_funct_1(D_258) | ~l1_pre_topc(C_257) | ~v2_pre_topc(C_257) | v2_struct_0(C_257) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.99/1.96  tff(c_24, plain, (~r1_tmap_1('#skF_6', '#skF_5', k1_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.99/1.96  tff(c_195, plain, (~r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9'), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_189, c_24])).
% 3.99/1.96  tff(c_199, plain, (~r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_58, c_56, c_42, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_195])).
% 3.99/1.96  tff(c_200, plain, (~r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_60, c_199])).
% 3.99/1.96  tff(c_201, plain, (~m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_200])).
% 3.99/1.96  tff(c_204, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_116, c_201])).
% 3.99/1.96  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_204])).
% 3.99/1.96  tff(c_209, plain, (~r1_tmap_1('#skF_4', '#skF_5', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_200])).
% 3.99/1.96  tff(c_219, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_186, c_209])).
% 3.99/1.96  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_219])).
% 3.99/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.96  
% 3.99/1.96  Inference rules
% 3.99/1.96  ----------------------
% 3.99/1.96  #Ref     : 0
% 3.99/1.96  #Sup     : 23
% 3.99/1.96  #Fact    : 0
% 3.99/1.96  #Define  : 0
% 3.99/1.96  #Split   : 6
% 3.99/1.96  #Chain   : 0
% 3.99/1.96  #Close   : 0
% 3.99/1.96  
% 3.99/1.96  Ordering : KBO
% 3.99/1.96  
% 3.99/1.96  Simplification rules
% 3.99/1.96  ----------------------
% 3.99/1.96  #Subsume      : 0
% 3.99/1.96  #Demod        : 60
% 3.99/1.96  #Tautology    : 3
% 3.99/1.96  #SimpNegUnit  : 13
% 3.99/1.96  #BackRed      : 0
% 3.99/1.96  
% 3.99/1.96  #Partial instantiations: 0
% 3.99/1.96  #Strategies tried      : 1
% 3.99/1.96  
% 3.99/1.96  Timing (in seconds)
% 3.99/1.96  ----------------------
% 3.99/1.96  Preprocessing        : 0.58
% 3.99/1.96  Parsing              : 0.30
% 3.99/1.96  CNF conversion       : 0.08
% 3.99/1.96  Main loop            : 0.41
% 3.99/1.96  Inferencing          : 0.15
% 3.99/1.96  Reduction            : 0.13
% 3.99/1.96  Demodulation         : 0.09
% 3.99/1.96  BG Simplification    : 0.03
% 3.99/1.96  Subsumption          : 0.07
% 3.99/1.96  Abstraction          : 0.01
% 3.99/1.96  MUC search           : 0.00
% 3.99/1.97  Cooper               : 0.00
% 3.99/1.97  Total                : 1.05
% 3.99/1.97  Index Insertion      : 0.00
% 3.99/1.97  Index Deletion       : 0.00
% 3.99/1.97  Index Matching       : 0.00
% 3.99/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
