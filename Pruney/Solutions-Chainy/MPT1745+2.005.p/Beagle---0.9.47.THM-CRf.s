%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:49 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 206 expanded)
%              Number of leaves         :   33 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  245 (1580 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(f_195,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_97,axiom,(
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

tff(f_148,axiom,(
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

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_28,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_20,plain,(
    v5_pre_topc('#skF_6','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_40,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_8,plain,(
    ! [B_12,A_10] :
      ( r2_hidden(B_12,k1_connsp_2(A_10,B_12))
      | ~ m1_subset_1(B_12,u1_struct_0(A_10))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_65,plain,(
    ! [A_224,B_225] :
      ( m1_subset_1(k1_connsp_2(A_224,B_225),k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_subset_1(B_225,u1_struct_0(A_224))
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_226,A_227,B_228] :
      ( ~ v1_xboole_0(u1_struct_0(A_226))
      | ~ r2_hidden(A_227,k1_connsp_2(A_226,B_228))
      | ~ m1_subset_1(B_228,u1_struct_0(A_226))
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_74,plain,(
    ! [A_229,B_230] :
      ( ~ v1_xboole_0(u1_struct_0(A_229))
      | ~ m1_subset_1(B_230,u1_struct_0(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_77,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_80,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_77])).

tff(c_81,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_80])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_82,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( m1_subset_1(k3_funct_2(A_231,B_232,C_233,D_234),B_232)
      | ~ m1_subset_1(D_234,A_231)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_2(C_233,A_231,B_232)
      | ~ v1_funct_1(C_233)
      | v1_xboole_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [D_234] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_234),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_89,plain,(
    ! [D_234] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_234),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_84])).

tff(c_90,plain,(
    ! [D_234] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_234),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_89])).

tff(c_128,plain,(
    ! [B_243,A_244,C_245,D_246] :
      ( r1_tmap_1(B_243,A_244,C_245,D_246)
      | ~ m1_subset_1(D_246,u1_struct_0(B_243))
      | ~ v5_pre_topc(C_245,B_243,A_244)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_243),u1_struct_0(A_244))))
      | ~ v1_funct_2(C_245,u1_struct_0(B_243),u1_struct_0(A_244))
      | ~ v1_funct_1(C_245)
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_132,plain,(
    ! [A_244,C_245,D_234] :
      ( r1_tmap_1('#skF_2',A_244,C_245,k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_234))
      | ~ v5_pre_topc(C_245,'#skF_2',A_244)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_244))))
      | ~ v1_funct_2(C_245,u1_struct_0('#skF_2'),u1_struct_0(A_244))
      | ~ v1_funct_1(C_245)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244)
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_90,c_128])).

tff(c_141,plain,(
    ! [A_244,C_245,D_234] :
      ( r1_tmap_1('#skF_2',A_244,C_245,k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_234))
      | ~ v5_pre_topc(C_245,'#skF_2',A_244)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_244))))
      | ~ v1_funct_2(C_245,u1_struct_0('#skF_2'),u1_struct_0(A_244))
      | ~ v1_funct_1(C_245)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244)
      | ~ m1_subset_1(D_234,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_132])).

tff(c_155,plain,(
    ! [A_249,C_250,D_251] :
      ( r1_tmap_1('#skF_2',A_249,C_250,k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_251))
      | ~ v5_pre_topc(C_250,'#skF_2',A_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_249))))
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_2'),u1_struct_0(A_249))
      | ~ v1_funct_1(C_250)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249)
      | ~ m1_subset_1(D_251,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_141])).

tff(c_157,plain,(
    ! [D_251] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_251))
      | ~ v5_pre_topc('#skF_6','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(D_251,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_160,plain,(
    ! [D_251] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_251))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(D_251,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_30,c_28,c_20,c_157])).

tff(c_161,plain,(
    ! [D_251] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_251))
      | ~ m1_subset_1(D_251,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_160])).

tff(c_22,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_164,plain,(
    ! [B_259,D_260,A_257,C_261,F_256,E_258] :
      ( r1_tmap_1(B_259,A_257,k1_partfun1(u1_struct_0(B_259),u1_struct_0(C_261),u1_struct_0(C_261),u1_struct_0(A_257),D_260,E_258),F_256)
      | ~ r1_tmap_1(C_261,A_257,E_258,k3_funct_2(u1_struct_0(B_259),u1_struct_0(C_261),D_260,F_256))
      | ~ r1_tmap_1(B_259,C_261,D_260,F_256)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_259),u1_struct_0(C_261),D_260,F_256),u1_struct_0(C_261))
      | ~ m1_subset_1(F_256,u1_struct_0(B_259))
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_261),u1_struct_0(A_257))))
      | ~ v1_funct_2(E_258,u1_struct_0(C_261),u1_struct_0(A_257))
      | ~ v1_funct_1(E_258)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_259),u1_struct_0(C_261))))
      | ~ v1_funct_2(D_260,u1_struct_0(B_259),u1_struct_0(C_261))
      | ~ v1_funct_1(D_260)
      | ~ l1_pre_topc(C_261)
      | ~ v2_pre_topc(C_261)
      | v2_struct_0(C_261)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_18,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k1_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_170,plain,
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
    inference(resolution,[status(thm)],[c_164,c_18])).

tff(c_174,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_52,c_50,c_36,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_170])).

tff(c_175,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_54,c_174])).

tff(c_176,plain,(
    ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_179,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_179])).

tff(c_184,plain,(
    ~ r1_tmap_1('#skF_2','#skF_3','#skF_6',k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_209,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_161,c_184])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.34  
% 2.69/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.34  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.69/1.34  
% 2.69/1.34  %Foreground sorts:
% 2.69/1.34  
% 2.69/1.34  
% 2.69/1.34  %Background operators:
% 2.69/1.34  
% 2.69/1.34  
% 2.69/1.34  %Foreground operators:
% 2.69/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.69/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.34  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 2.69/1.34  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.69/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.69/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.69/1.34  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.34  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.69/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.69/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.69/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.34  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.69/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.34  
% 2.69/1.36  tff(f_195, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => ((r1_tmap_1(C, A, D, F) & v5_pre_topc(E, A, B)) => r1_tmap_1(C, B, k1_partfun1(u1_struct_0(C), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), D, E), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tmap_1)).
% 2.69/1.36  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 2.69/1.36  tff(f_56, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 2.69/1.36  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.69/1.36  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.69/1.36  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 2.69/1.36  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 2.69/1.36  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_28, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_20, plain, (v5_pre_topc('#skF_6', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_40, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_8, plain, (![B_12, A_10]: (r2_hidden(B_12, k1_connsp_2(A_10, B_12)) | ~m1_subset_1(B_12, u1_struct_0(A_10)) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.36  tff(c_65, plain, (![A_224, B_225]: (m1_subset_1(k1_connsp_2(A_224, B_225), k1_zfmisc_1(u1_struct_0(A_224))) | ~m1_subset_1(B_225, u1_struct_0(A_224)) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.36  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.36  tff(c_69, plain, (![A_226, A_227, B_228]: (~v1_xboole_0(u1_struct_0(A_226)) | ~r2_hidden(A_227, k1_connsp_2(A_226, B_228)) | ~m1_subset_1(B_228, u1_struct_0(A_226)) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.69/1.36  tff(c_74, plain, (![A_229, B_230]: (~v1_xboole_0(u1_struct_0(A_229)) | ~m1_subset_1(B_230, u1_struct_0(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_8, c_69])).
% 2.69/1.36  tff(c_77, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_74])).
% 2.69/1.36  tff(c_80, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_77])).
% 2.69/1.36  tff(c_81, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_80])).
% 2.69/1.36  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_82, plain, (![A_231, B_232, C_233, D_234]: (m1_subset_1(k3_funct_2(A_231, B_232, C_233, D_234), B_232) | ~m1_subset_1(D_234, A_231) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_2(C_233, A_231, B_232) | ~v1_funct_1(C_233) | v1_xboole_0(A_231))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.36  tff(c_84, plain, (![D_234]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_234), u1_struct_0('#skF_2')) | ~m1_subset_1(D_234, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_32, c_82])).
% 2.69/1.36  tff(c_89, plain, (![D_234]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_234), u1_struct_0('#skF_2')) | ~m1_subset_1(D_234, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_84])).
% 2.69/1.36  tff(c_90, plain, (![D_234]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_234), u1_struct_0('#skF_2')) | ~m1_subset_1(D_234, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_81, c_89])).
% 2.69/1.36  tff(c_128, plain, (![B_243, A_244, C_245, D_246]: (r1_tmap_1(B_243, A_244, C_245, D_246) | ~m1_subset_1(D_246, u1_struct_0(B_243)) | ~v5_pre_topc(C_245, B_243, A_244) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_243), u1_struct_0(A_244)))) | ~v1_funct_2(C_245, u1_struct_0(B_243), u1_struct_0(A_244)) | ~v1_funct_1(C_245) | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.36  tff(c_132, plain, (![A_244, C_245, D_234]: (r1_tmap_1('#skF_2', A_244, C_245, k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_234)) | ~v5_pre_topc(C_245, '#skF_2', A_244) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_244)))) | ~v1_funct_2(C_245, u1_struct_0('#skF_2'), u1_struct_0(A_244)) | ~v1_funct_1(C_245) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244) | ~m1_subset_1(D_234, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_90, c_128])).
% 2.69/1.36  tff(c_141, plain, (![A_244, C_245, D_234]: (r1_tmap_1('#skF_2', A_244, C_245, k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_234)) | ~v5_pre_topc(C_245, '#skF_2', A_244) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_244)))) | ~v1_funct_2(C_245, u1_struct_0('#skF_2'), u1_struct_0(A_244)) | ~v1_funct_1(C_245) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244) | ~m1_subset_1(D_234, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_132])).
% 2.69/1.36  tff(c_155, plain, (![A_249, C_250, D_251]: (r1_tmap_1('#skF_2', A_249, C_250, k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_251)) | ~v5_pre_topc(C_250, '#skF_2', A_249) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_249)))) | ~v1_funct_2(C_250, u1_struct_0('#skF_2'), u1_struct_0(A_249)) | ~v1_funct_1(C_250) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249) | ~m1_subset_1(D_251, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_141])).
% 2.69/1.36  tff(c_157, plain, (![D_251]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_251)) | ~v5_pre_topc('#skF_6', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(D_251, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_26, c_155])).
% 2.69/1.36  tff(c_160, plain, (![D_251]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_251)) | v2_struct_0('#skF_3') | ~m1_subset_1(D_251, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_30, c_28, c_20, c_157])).
% 2.69/1.36  tff(c_161, plain, (![D_251]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_251)) | ~m1_subset_1(D_251, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_160])).
% 2.69/1.36  tff(c_22, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_164, plain, (![B_259, D_260, A_257, C_261, F_256, E_258]: (r1_tmap_1(B_259, A_257, k1_partfun1(u1_struct_0(B_259), u1_struct_0(C_261), u1_struct_0(C_261), u1_struct_0(A_257), D_260, E_258), F_256) | ~r1_tmap_1(C_261, A_257, E_258, k3_funct_2(u1_struct_0(B_259), u1_struct_0(C_261), D_260, F_256)) | ~r1_tmap_1(B_259, C_261, D_260, F_256) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_259), u1_struct_0(C_261), D_260, F_256), u1_struct_0(C_261)) | ~m1_subset_1(F_256, u1_struct_0(B_259)) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_261), u1_struct_0(A_257)))) | ~v1_funct_2(E_258, u1_struct_0(C_261), u1_struct_0(A_257)) | ~v1_funct_1(E_258) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_259), u1_struct_0(C_261)))) | ~v1_funct_2(D_260, u1_struct_0(B_259), u1_struct_0(C_261)) | ~v1_funct_1(D_260) | ~l1_pre_topc(C_261) | ~v2_pre_topc(C_261) | v2_struct_0(C_261) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.69/1.36  tff(c_18, plain, (~r1_tmap_1('#skF_4', '#skF_3', k1_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 2.69/1.36  tff(c_170, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_164, c_18])).
% 2.69/1.36  tff(c_174, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_52, c_50, c_36, c_34, c_32, c_30, c_28, c_26, c_24, c_22, c_170])).
% 2.69/1.36  tff(c_175, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_54, c_174])).
% 2.69/1.36  tff(c_176, plain, (~m1_subset_1(k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_175])).
% 2.69/1.36  tff(c_179, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_176])).
% 2.69/1.36  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_179])).
% 2.69/1.36  tff(c_184, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_6', k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_175])).
% 2.69/1.36  tff(c_209, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_161, c_184])).
% 2.69/1.36  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_209])).
% 2.69/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.36  
% 2.69/1.36  Inference rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Ref     : 0
% 2.69/1.36  #Sup     : 23
% 2.69/1.36  #Fact    : 0
% 2.69/1.36  #Define  : 0
% 2.69/1.36  #Split   : 6
% 2.69/1.36  #Chain   : 0
% 2.69/1.36  #Close   : 0
% 2.69/1.36  
% 2.69/1.36  Ordering : KBO
% 2.69/1.36  
% 2.69/1.36  Simplification rules
% 2.69/1.36  ----------------------
% 2.69/1.36  #Subsume      : 2
% 2.69/1.36  #Demod        : 65
% 2.69/1.36  #Tautology    : 2
% 2.69/1.36  #SimpNegUnit  : 16
% 2.69/1.36  #BackRed      : 0
% 2.69/1.36  
% 2.69/1.36  #Partial instantiations: 0
% 2.69/1.36  #Strategies tried      : 1
% 2.69/1.36  
% 2.69/1.36  Timing (in seconds)
% 2.69/1.36  ----------------------
% 2.69/1.37  Preprocessing        : 0.35
% 2.69/1.37  Parsing              : 0.19
% 2.69/1.37  CNF conversion       : 0.04
% 2.69/1.37  Main loop            : 0.24
% 2.69/1.37  Inferencing          : 0.09
% 2.69/1.37  Reduction            : 0.08
% 2.69/1.37  Demodulation         : 0.06
% 2.69/1.37  BG Simplification    : 0.02
% 2.69/1.37  Subsumption          : 0.04
% 2.69/1.37  Abstraction          : 0.01
% 2.69/1.37  MUC search           : 0.00
% 2.69/1.37  Cooper               : 0.00
% 2.69/1.37  Total                : 0.63
% 2.69/1.37  Index Insertion      : 0.00
% 2.69/1.37  Index Deletion       : 0.00
% 2.69/1.37  Index Matching       : 0.00
% 2.69/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
