%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:19 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 465 expanded)
%              Number of leaves         :   40 ( 193 expanded)
%              Depth                    :   13
%              Number of atoms          :  381 (3874 expanded)
%              Number of equality atoms :   49 ( 241 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_113,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_46,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_40,plain,(
    '#skF_6' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_44,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_91,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_92,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_38,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_93,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_1080,plain,(
    ! [C_342,D_343,A_347,B_344,E_346,F_345] :
      ( F_345 = E_346
      | ~ r1_funct_2(A_347,B_344,C_342,D_343,E_346,F_345)
      | ~ m1_subset_1(F_345,k1_zfmisc_1(k2_zfmisc_1(C_342,D_343)))
      | ~ v1_funct_2(F_345,C_342,D_343)
      | ~ v1_funct_1(F_345)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_347,B_344)))
      | ~ v1_funct_2(E_346,A_347,B_344)
      | ~ v1_funct_1(E_346)
      | v1_xboole_0(D_343)
      | v1_xboole_0(B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1082,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_93,c_1080])).

tff(c_1085,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_46,c_91,c_92,c_1082])).

tff(c_1086,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1085])).

tff(c_211,plain,(
    ! [A_227] :
      ( m1_subset_1('#skF_2'(A_227),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_219,plain,(
    ! [A_228] :
      ( r1_tarski('#skF_2'(A_228),u1_struct_0(A_228))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_211,c_14])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_148,plain,(
    ! [C_211,B_212,A_213] :
      ( ~ v1_xboole_0(C_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(C_211))
      | ~ r2_hidden(A_213,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_161,plain,(
    ! [B_214,A_215,A_216] :
      ( ~ v1_xboole_0(B_214)
      | ~ r2_hidden(A_215,A_216)
      | ~ r1_tarski(A_216,B_214) ) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_165,plain,(
    ! [B_217,A_218,B_219] :
      ( ~ v1_xboole_0(B_217)
      | ~ r1_tarski(A_218,B_217)
      | r1_tarski(A_218,B_219) ) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_179,plain,(
    ! [B_221,B_222] :
      ( ~ v1_xboole_0(B_221)
      | r1_tarski(B_221,B_222) ) ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_185,plain,(
    ! [B_222,B_221] :
      ( B_222 = B_221
      | ~ r1_tarski(B_222,B_221)
      | ~ v1_xboole_0(B_221) ) ),
    inference(resolution,[status(thm)],[c_179,c_8])).

tff(c_227,plain,(
    ! [A_228] :
      ( u1_struct_0(A_228) = '#skF_2'(A_228)
      | ~ v1_xboole_0(u1_struct_0(A_228))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_219,c_185])).

tff(c_1091,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1086,c_227])).

tff(c_1097,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1091])).

tff(c_1098,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1097])).

tff(c_1100,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1086])).

tff(c_22,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0('#skF_2'(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1156,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1100,c_22])).

tff(c_1161,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1156])).

tff(c_1163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1161])).

tff(c_1164,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1085])).

tff(c_396,plain,(
    ! [F_264,A_266,C_261,D_262,E_265,B_263] :
      ( F_264 = E_265
      | ~ r1_funct_2(A_266,B_263,C_261,D_262,E_265,F_264)
      | ~ m1_subset_1(F_264,k1_zfmisc_1(k2_zfmisc_1(C_261,D_262)))
      | ~ v1_funct_2(F_264,C_261,D_262)
      | ~ v1_funct_1(F_264)
      | ~ m1_subset_1(E_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_263)))
      | ~ v1_funct_2(E_265,A_266,B_263)
      | ~ v1_funct_1(E_265)
      | v1_xboole_0(D_262)
      | v1_xboole_0(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_398,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_93,c_396])).

tff(c_401,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_46,c_91,c_92,c_398])).

tff(c_402,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_407,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_227])).

tff(c_413,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_407])).

tff(c_414,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_413])).

tff(c_416,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_402])).

tff(c_469,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_416,c_22])).

tff(c_474,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_469])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_474])).

tff(c_477,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_86,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_88,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_86])).

tff(c_230,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_480,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_230])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_76,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_89,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60])).

tff(c_618,plain,(
    ! [B_278,C_282,A_280,D_281,E_279] :
      ( k3_tmap_1(A_280,B_278,C_282,D_281,E_279) = k2_partfun1(u1_struct_0(C_282),u1_struct_0(B_278),E_279,u1_struct_0(D_281))
      | ~ m1_pre_topc(D_281,C_282)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_282),u1_struct_0(B_278))))
      | ~ v1_funct_2(E_279,u1_struct_0(C_282),u1_struct_0(B_278))
      | ~ v1_funct_1(E_279)
      | ~ m1_pre_topc(D_281,A_280)
      | ~ m1_pre_topc(C_282,A_280)
      | ~ l1_pre_topc(B_278)
      | ~ v2_pre_topc(B_278)
      | v2_struct_0(B_278)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_620,plain,(
    ! [A_280,D_281] :
      ( k3_tmap_1(A_280,'#skF_4','#skF_3',D_281,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_281))
      | ~ m1_pre_topc(D_281,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_281,A_280)
      | ~ m1_pre_topc('#skF_3',A_280)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_92,c_618])).

tff(c_628,plain,(
    ! [A_280,D_281] :
      ( k3_tmap_1(A_280,'#skF_4','#skF_3',D_281,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_281))
      | ~ m1_pre_topc(D_281,'#skF_3')
      | ~ m1_pre_topc(D_281,A_280)
      | ~ m1_pre_topc('#skF_3',A_280)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46,c_91,c_620])).

tff(c_801,plain,(
    ! [A_304,D_305] :
      ( k3_tmap_1(A_304,'#skF_4','#skF_3',D_305,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_305))
      | ~ m1_pre_topc(D_305,'#skF_3')
      | ~ m1_pre_topc(D_305,A_304)
      | ~ m1_pre_topc('#skF_3',A_304)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304)
      | v2_struct_0(A_304) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_628])).

tff(c_809,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_801])).

tff(c_820,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_89,c_64,c_809])).

tff(c_821,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_820])).

tff(c_518,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k2_partfun1(u1_struct_0(A_268),u1_struct_0(B_269),C_270,u1_struct_0(D_271)) = k2_tmap_1(A_268,B_269,C_270,D_271)
      | ~ m1_pre_topc(D_271,A_268)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_268),u1_struct_0(B_269))))
      | ~ v1_funct_2(C_270,u1_struct_0(A_268),u1_struct_0(B_269))
      | ~ v1_funct_1(C_270)
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_520,plain,(
    ! [D_271] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_271)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_271)
      | ~ m1_pre_topc(D_271,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_92,c_518])).

tff(c_528,plain,(
    ! [D_271] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_271)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_271)
      | ~ m1_pre_topc(D_271,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_46,c_91,c_520])).

tff(c_529,plain,(
    ! [D_271] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_271)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_271)
      | ~ m1_pre_topc(D_271,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_528])).

tff(c_861,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_529])).

tff(c_868,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_861])).

tff(c_80,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_90,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_80])).

tff(c_288,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_90])).

tff(c_882,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_288])).

tff(c_885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_882])).

tff(c_887,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1169,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_887])).

tff(c_1290,plain,(
    ! [D_361,B_358,C_362,A_360,E_359] :
      ( k3_tmap_1(A_360,B_358,C_362,D_361,E_359) = k2_partfun1(u1_struct_0(C_362),u1_struct_0(B_358),E_359,u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,C_362)
      | ~ m1_subset_1(E_359,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_362),u1_struct_0(B_358))))
      | ~ v1_funct_2(E_359,u1_struct_0(C_362),u1_struct_0(B_358))
      | ~ v1_funct_1(E_359)
      | ~ m1_pre_topc(D_361,A_360)
      | ~ m1_pre_topc(C_362,A_360)
      | ~ l1_pre_topc(B_358)
      | ~ v2_pre_topc(B_358)
      | v2_struct_0(B_358)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1292,plain,(
    ! [A_360,D_361] :
      ( k3_tmap_1(A_360,'#skF_4','#skF_3',D_361,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_361,A_360)
      | ~ m1_pre_topc('#skF_3',A_360)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_92,c_1290])).

tff(c_1300,plain,(
    ! [A_360,D_361] :
      ( k3_tmap_1(A_360,'#skF_4','#skF_3',D_361,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_361))
      | ~ m1_pre_topc(D_361,'#skF_3')
      | ~ m1_pre_topc(D_361,A_360)
      | ~ m1_pre_topc('#skF_3',A_360)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46,c_91,c_1292])).

tff(c_1441,plain,(
    ! [A_380,D_381] :
      ( k3_tmap_1(A_380,'#skF_4','#skF_3',D_381,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_381))
      | ~ m1_pre_topc(D_381,'#skF_3')
      | ~ m1_pre_topc(D_381,A_380)
      | ~ m1_pre_topc('#skF_3',A_380)
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1300])).

tff(c_1449,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1441])).

tff(c_1460,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_89,c_64,c_1449])).

tff(c_1461,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1460])).

tff(c_1200,plain,(
    ! [A_349,B_350,C_351,D_352] :
      ( k2_partfun1(u1_struct_0(A_349),u1_struct_0(B_350),C_351,u1_struct_0(D_352)) = k2_tmap_1(A_349,B_350,C_351,D_352)
      | ~ m1_pre_topc(D_352,A_349)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_349),u1_struct_0(B_350))))
      | ~ v1_funct_2(C_351,u1_struct_0(A_349),u1_struct_0(B_350))
      | ~ v1_funct_1(C_351)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1202,plain,(
    ! [D_352] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_352)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_352)
      | ~ m1_pre_topc(D_352,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_92,c_1200])).

tff(c_1210,plain,(
    ! [D_352] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_352)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_352)
      | ~ m1_pre_topc(D_352,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_46,c_91,c_1202])).

tff(c_1211,plain,(
    ! [D_352] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_352)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_352)
      | ~ m1_pre_topc(D_352,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_1210])).

tff(c_1501,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_1211])).

tff(c_1508,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1501])).

tff(c_886,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1515,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_886])).

tff(c_1517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1169,c_1515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.75  
% 4.16/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.76  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.51/1.76  
% 4.51/1.76  %Foreground sorts:
% 4.51/1.76  
% 4.51/1.76  
% 4.51/1.76  %Background operators:
% 4.51/1.76  
% 4.51/1.76  
% 4.51/1.76  %Foreground operators:
% 4.51/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.51/1.76  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.51/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.76  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.51/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.76  tff('#skF_9', type, '#skF_9': $i).
% 4.51/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.51/1.76  tff('#skF_8', type, '#skF_8': $i).
% 4.51/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.76  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 4.51/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.51/1.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.51/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.51/1.76  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.51/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.51/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.76  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.51/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.76  
% 4.61/1.79  tff(f_218, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 4.61/1.79  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 4.61/1.79  tff(f_64, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.61/1.79  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.61/1.79  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.61/1.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.61/1.79  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.61/1.79  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.61/1.79  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.61/1.79  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_56, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_46, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_40, plain, ('#skF_6'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_44, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_91, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 4.61/1.79  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_92, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 4.61/1.79  tff(c_38, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_93, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 4.61/1.79  tff(c_1080, plain, (![C_342, D_343, A_347, B_344, E_346, F_345]: (F_345=E_346 | ~r1_funct_2(A_347, B_344, C_342, D_343, E_346, F_345) | ~m1_subset_1(F_345, k1_zfmisc_1(k2_zfmisc_1(C_342, D_343))) | ~v1_funct_2(F_345, C_342, D_343) | ~v1_funct_1(F_345) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_347, B_344))) | ~v1_funct_2(E_346, A_347, B_344) | ~v1_funct_1(E_346) | v1_xboole_0(D_343) | v1_xboole_0(B_344))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.61/1.79  tff(c_1082, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_93, c_1080])).
% 4.61/1.79  tff(c_1085, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_46, c_91, c_92, c_1082])).
% 4.61/1.79  tff(c_1086, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1085])).
% 4.61/1.79  tff(c_211, plain, (![A_227]: (m1_subset_1('#skF_2'(A_227), k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.61/1.79  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.61/1.79  tff(c_219, plain, (![A_228]: (r1_tarski('#skF_2'(A_228), u1_struct_0(A_228)) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_211, c_14])).
% 4.61/1.79  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.61/1.79  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.61/1.79  tff(c_148, plain, (![C_211, B_212, A_213]: (~v1_xboole_0(C_211) | ~m1_subset_1(B_212, k1_zfmisc_1(C_211)) | ~r2_hidden(A_213, B_212))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.61/1.79  tff(c_161, plain, (![B_214, A_215, A_216]: (~v1_xboole_0(B_214) | ~r2_hidden(A_215, A_216) | ~r1_tarski(A_216, B_214))), inference(resolution, [status(thm)], [c_16, c_148])).
% 4.61/1.79  tff(c_165, plain, (![B_217, A_218, B_219]: (~v1_xboole_0(B_217) | ~r1_tarski(A_218, B_217) | r1_tarski(A_218, B_219))), inference(resolution, [status(thm)], [c_6, c_161])).
% 4.61/1.79  tff(c_179, plain, (![B_221, B_222]: (~v1_xboole_0(B_221) | r1_tarski(B_221, B_222))), inference(resolution, [status(thm)], [c_12, c_165])).
% 4.61/1.79  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.61/1.79  tff(c_185, plain, (![B_222, B_221]: (B_222=B_221 | ~r1_tarski(B_222, B_221) | ~v1_xboole_0(B_221))), inference(resolution, [status(thm)], [c_179, c_8])).
% 4.61/1.79  tff(c_227, plain, (![A_228]: (u1_struct_0(A_228)='#skF_2'(A_228) | ~v1_xboole_0(u1_struct_0(A_228)) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_219, c_185])).
% 4.61/1.79  tff(c_1091, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1086, c_227])).
% 4.61/1.79  tff(c_1097, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1091])).
% 4.61/1.79  tff(c_1098, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_1097])).
% 4.61/1.79  tff(c_1100, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1086])).
% 4.61/1.79  tff(c_22, plain, (![A_13]: (~v1_xboole_0('#skF_2'(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.61/1.79  tff(c_1156, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1100, c_22])).
% 4.61/1.79  tff(c_1161, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1156])).
% 4.61/1.79  tff(c_1163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1161])).
% 4.61/1.79  tff(c_1164, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_1085])).
% 4.61/1.79  tff(c_396, plain, (![F_264, A_266, C_261, D_262, E_265, B_263]: (F_264=E_265 | ~r1_funct_2(A_266, B_263, C_261, D_262, E_265, F_264) | ~m1_subset_1(F_264, k1_zfmisc_1(k2_zfmisc_1(C_261, D_262))) | ~v1_funct_2(F_264, C_261, D_262) | ~v1_funct_1(F_264) | ~m1_subset_1(E_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_263))) | ~v1_funct_2(E_265, A_266, B_263) | ~v1_funct_1(E_265) | v1_xboole_0(D_262) | v1_xboole_0(B_263))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.61/1.79  tff(c_398, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_93, c_396])).
% 4.61/1.79  tff(c_401, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_46, c_91, c_92, c_398])).
% 4.61/1.79  tff(c_402, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_401])).
% 4.61/1.79  tff(c_407, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_402, c_227])).
% 4.61/1.79  tff(c_413, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_407])).
% 4.61/1.79  tff(c_414, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_413])).
% 4.61/1.79  tff(c_416, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_402])).
% 4.61/1.79  tff(c_469, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_416, c_22])).
% 4.61/1.79  tff(c_474, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_469])).
% 4.61/1.79  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_474])).
% 4.61/1.79  tff(c_477, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_401])).
% 4.61/1.79  tff(c_86, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_88, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_86])).
% 4.61/1.79  tff(c_230, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_88])).
% 4.61/1.79  tff(c_480, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_230])).
% 4.61/1.79  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_76, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_89, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60])).
% 4.61/1.79  tff(c_618, plain, (![B_278, C_282, A_280, D_281, E_279]: (k3_tmap_1(A_280, B_278, C_282, D_281, E_279)=k2_partfun1(u1_struct_0(C_282), u1_struct_0(B_278), E_279, u1_struct_0(D_281)) | ~m1_pre_topc(D_281, C_282) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_282), u1_struct_0(B_278)))) | ~v1_funct_2(E_279, u1_struct_0(C_282), u1_struct_0(B_278)) | ~v1_funct_1(E_279) | ~m1_pre_topc(D_281, A_280) | ~m1_pre_topc(C_282, A_280) | ~l1_pre_topc(B_278) | ~v2_pre_topc(B_278) | v2_struct_0(B_278) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.61/1.79  tff(c_620, plain, (![A_280, D_281]: (k3_tmap_1(A_280, '#skF_4', '#skF_3', D_281, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_281)) | ~m1_pre_topc(D_281, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_281, A_280) | ~m1_pre_topc('#skF_3', A_280) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_92, c_618])).
% 4.61/1.79  tff(c_628, plain, (![A_280, D_281]: (k3_tmap_1(A_280, '#skF_4', '#skF_3', D_281, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_281)) | ~m1_pre_topc(D_281, '#skF_3') | ~m1_pre_topc(D_281, A_280) | ~m1_pre_topc('#skF_3', A_280) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46, c_91, c_620])).
% 4.61/1.79  tff(c_801, plain, (![A_304, D_305]: (k3_tmap_1(A_304, '#skF_4', '#skF_3', D_305, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_305)) | ~m1_pre_topc(D_305, '#skF_3') | ~m1_pre_topc(D_305, A_304) | ~m1_pre_topc('#skF_3', A_304) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304) | v2_struct_0(A_304))), inference(negUnitSimplification, [status(thm)], [c_72, c_628])).
% 4.61/1.79  tff(c_809, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_801])).
% 4.61/1.79  tff(c_820, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_89, c_64, c_809])).
% 4.61/1.79  tff(c_821, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_78, c_820])).
% 4.61/1.79  tff(c_518, plain, (![A_268, B_269, C_270, D_271]: (k2_partfun1(u1_struct_0(A_268), u1_struct_0(B_269), C_270, u1_struct_0(D_271))=k2_tmap_1(A_268, B_269, C_270, D_271) | ~m1_pre_topc(D_271, A_268) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_268), u1_struct_0(B_269)))) | ~v1_funct_2(C_270, u1_struct_0(A_268), u1_struct_0(B_269)) | ~v1_funct_1(C_270) | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.61/1.79  tff(c_520, plain, (![D_271]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_271))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_271) | ~m1_pre_topc(D_271, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_92, c_518])).
% 4.61/1.79  tff(c_528, plain, (![D_271]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_271))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_271) | ~m1_pre_topc(D_271, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_46, c_91, c_520])).
% 4.61/1.79  tff(c_529, plain, (![D_271]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_271))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_271) | ~m1_pre_topc(D_271, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_528])).
% 4.61/1.79  tff(c_861, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_821, c_529])).
% 4.61/1.79  tff(c_868, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_861])).
% 4.61/1.79  tff(c_80, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.61/1.79  tff(c_90, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_80])).
% 4.61/1.79  tff(c_288, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_90])).
% 4.61/1.79  tff(c_882, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_868, c_288])).
% 4.61/1.79  tff(c_885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_480, c_882])).
% 4.61/1.79  tff(c_887, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_88])).
% 4.61/1.79  tff(c_1169, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_887])).
% 4.61/1.79  tff(c_1290, plain, (![D_361, B_358, C_362, A_360, E_359]: (k3_tmap_1(A_360, B_358, C_362, D_361, E_359)=k2_partfun1(u1_struct_0(C_362), u1_struct_0(B_358), E_359, u1_struct_0(D_361)) | ~m1_pre_topc(D_361, C_362) | ~m1_subset_1(E_359, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_362), u1_struct_0(B_358)))) | ~v1_funct_2(E_359, u1_struct_0(C_362), u1_struct_0(B_358)) | ~v1_funct_1(E_359) | ~m1_pre_topc(D_361, A_360) | ~m1_pre_topc(C_362, A_360) | ~l1_pre_topc(B_358) | ~v2_pre_topc(B_358) | v2_struct_0(B_358) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.61/1.79  tff(c_1292, plain, (![A_360, D_361]: (k3_tmap_1(A_360, '#skF_4', '#skF_3', D_361, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_361)) | ~m1_pre_topc(D_361, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_361, A_360) | ~m1_pre_topc('#skF_3', A_360) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(resolution, [status(thm)], [c_92, c_1290])).
% 4.61/1.79  tff(c_1300, plain, (![A_360, D_361]: (k3_tmap_1(A_360, '#skF_4', '#skF_3', D_361, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_361)) | ~m1_pre_topc(D_361, '#skF_3') | ~m1_pre_topc(D_361, A_360) | ~m1_pre_topc('#skF_3', A_360) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46, c_91, c_1292])).
% 4.61/1.79  tff(c_1441, plain, (![A_380, D_381]: (k3_tmap_1(A_380, '#skF_4', '#skF_3', D_381, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_381)) | ~m1_pre_topc(D_381, '#skF_3') | ~m1_pre_topc(D_381, A_380) | ~m1_pre_topc('#skF_3', A_380) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(negUnitSimplification, [status(thm)], [c_72, c_1300])).
% 4.61/1.79  tff(c_1449, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1441])).
% 4.61/1.79  tff(c_1460, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_89, c_64, c_1449])).
% 4.61/1.79  tff(c_1461, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_78, c_1460])).
% 4.61/1.79  tff(c_1200, plain, (![A_349, B_350, C_351, D_352]: (k2_partfun1(u1_struct_0(A_349), u1_struct_0(B_350), C_351, u1_struct_0(D_352))=k2_tmap_1(A_349, B_350, C_351, D_352) | ~m1_pre_topc(D_352, A_349) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_349), u1_struct_0(B_350)))) | ~v1_funct_2(C_351, u1_struct_0(A_349), u1_struct_0(B_350)) | ~v1_funct_1(C_351) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.61/1.79  tff(c_1202, plain, (![D_352]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_352))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_352) | ~m1_pre_topc(D_352, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_92, c_1200])).
% 4.61/1.79  tff(c_1210, plain, (![D_352]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_352))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_352) | ~m1_pre_topc(D_352, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_46, c_91, c_1202])).
% 4.61/1.79  tff(c_1211, plain, (![D_352]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_352))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_352) | ~m1_pre_topc(D_352, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_1210])).
% 4.61/1.79  tff(c_1501, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1461, c_1211])).
% 4.61/1.79  tff(c_1508, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1501])).
% 4.61/1.79  tff(c_886, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_88])).
% 4.61/1.79  tff(c_1515, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1508, c_886])).
% 4.61/1.79  tff(c_1517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1169, c_1515])).
% 4.61/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.79  
% 4.61/1.79  Inference rules
% 4.61/1.79  ----------------------
% 4.61/1.79  #Ref     : 0
% 4.61/1.79  #Sup     : 312
% 4.61/1.79  #Fact    : 0
% 4.61/1.79  #Define  : 0
% 4.61/1.79  #Split   : 17
% 4.61/1.79  #Chain   : 0
% 4.61/1.79  #Close   : 0
% 4.61/1.79  
% 4.61/1.79  Ordering : KBO
% 4.61/1.79  
% 4.61/1.79  Simplification rules
% 4.61/1.79  ----------------------
% 4.61/1.79  #Subsume      : 129
% 4.61/1.79  #Demod        : 243
% 4.61/1.79  #Tautology    : 73
% 4.61/1.79  #SimpNegUnit  : 34
% 4.61/1.79  #BackRed      : 63
% 4.61/1.79  
% 4.61/1.79  #Partial instantiations: 0
% 4.61/1.79  #Strategies tried      : 1
% 4.61/1.79  
% 4.61/1.79  Timing (in seconds)
% 4.61/1.79  ----------------------
% 4.61/1.80  Preprocessing        : 0.38
% 4.61/1.80  Parsing              : 0.19
% 4.61/1.80  CNF conversion       : 0.05
% 4.61/1.80  Main loop            : 0.61
% 4.61/1.80  Inferencing          : 0.19
% 4.61/1.80  Reduction            : 0.21
% 4.61/1.80  Demodulation         : 0.15
% 4.61/1.80  BG Simplification    : 0.03
% 4.61/1.80  Subsumption          : 0.13
% 4.61/1.80  Abstraction          : 0.03
% 4.61/1.80  MUC search           : 0.00
% 4.61/1.80  Cooper               : 0.00
% 4.61/1.80  Total                : 1.07
% 4.61/1.80  Index Insertion      : 0.00
% 4.61/1.80  Index Deletion       : 0.00
% 4.61/1.80  Index Matching       : 0.00
% 4.61/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
