%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:19 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 779 expanded)
%              Number of leaves         :   37 ( 295 expanded)
%              Depth                    :   12
%              Number of atoms          :  506 (6043 expanded)
%              Number of equality atoms :   70 ( 374 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_199,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
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

tff(f_130,axiom,(
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

tff(f_98,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    '#skF_5' = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_110,plain,(
    ! [C_204,B_205,A_206] :
      ( ~ v1_xboole_0(C_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(C_204))
      | ~ r2_hidden(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_117,plain,(
    ! [A_206] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_206,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_82,c_110])).

tff(c_120,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_124,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_120])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_36,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_34,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_81,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_28,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_83,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_357,plain,(
    ! [A_269,B_267,F_265,C_270,D_266,E_268] :
      ( F_265 = E_268
      | ~ r1_funct_2(A_269,B_267,C_270,D_266,E_268,F_265)
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(C_270,D_266)))
      | ~ v1_funct_2(F_265,C_270,D_266)
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_267)))
      | ~ v1_funct_2(E_268,A_269,B_267)
      | ~ v1_funct_1(E_268)
      | v1_xboole_0(D_266)
      | v1_xboole_0(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_365,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_357])).

tff(c_383,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_81,c_82,c_365])).

tff(c_384,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_383])).

tff(c_181,plain,(
    ! [A_233,C_234,F_229,E_232,B_231,D_230] :
      ( F_229 = E_232
      | ~ r1_funct_2(A_233,B_231,C_234,D_230,E_232,F_229)
      | ~ m1_subset_1(F_229,k1_zfmisc_1(k2_zfmisc_1(C_234,D_230)))
      | ~ v1_funct_2(F_229,C_234,D_230)
      | ~ v1_funct_1(F_229)
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_231)))
      | ~ v1_funct_2(E_232,A_233,B_231)
      | ~ v1_funct_1(E_232)
      | v1_xboole_0(D_230)
      | v1_xboole_0(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_189,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_181])).

tff(c_207,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_81,c_82,c_189])).

tff(c_208,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_207])).

tff(c_70,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_80,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_70])).

tff(c_146,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_76,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_78,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_76])).

tff(c_158,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_78])).

tff(c_229,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_158])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_79,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_50])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_259,plain,(
    ! [E_244,D_243,C_242,A_240,B_241] :
      ( k3_tmap_1(A_240,B_241,C_242,D_243,E_244) = k2_partfun1(u1_struct_0(C_242),u1_struct_0(B_241),E_244,u1_struct_0(D_243))
      | ~ m1_pre_topc(D_243,C_242)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_242),u1_struct_0(B_241))))
      | ~ v1_funct_2(E_244,u1_struct_0(C_242),u1_struct_0(B_241))
      | ~ v1_funct_1(E_244)
      | ~ m1_pre_topc(D_243,A_240)
      | ~ m1_pre_topc(C_242,A_240)
      | ~ l1_pre_topc(B_241)
      | ~ v2_pre_topc(B_241)
      | v2_struct_0(B_241)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_261,plain,(
    ! [A_240,D_243] :
      ( k3_tmap_1(A_240,'#skF_3','#skF_2',D_243,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_243))
      | ~ m1_pre_topc(D_243,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_243,A_240)
      | ~ m1_pre_topc('#skF_2',A_240)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_82,c_259])).

tff(c_266,plain,(
    ! [A_240,D_243] :
      ( k3_tmap_1(A_240,'#skF_3','#skF_2',D_243,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_243))
      | ~ m1_pre_topc(D_243,'#skF_2')
      | ~ m1_pre_topc(D_243,A_240)
      | ~ m1_pre_topc('#skF_2',A_240)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_261])).

tff(c_272,plain,(
    ! [A_245,D_246] :
      ( k3_tmap_1(A_245,'#skF_3','#skF_2',D_246,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_246))
      | ~ m1_pre_topc(D_246,'#skF_2')
      | ~ m1_pre_topc(D_246,A_245)
      | ~ m1_pre_topc('#skF_2',A_245)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_266])).

tff(c_274,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_272])).

tff(c_279,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_274])).

tff(c_280,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_279])).

tff(c_209,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( k2_partfun1(u1_struct_0(A_235),u1_struct_0(B_236),C_237,u1_struct_0(D_238)) = k2_tmap_1(A_235,B_236,C_237,D_238)
      | ~ m1_pre_topc(D_238,A_235)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),u1_struct_0(B_236))))
      | ~ v1_funct_2(C_237,u1_struct_0(A_235),u1_struct_0(B_236))
      | ~ v1_funct_1(C_237)
      | ~ l1_pre_topc(B_236)
      | ~ v2_pre_topc(B_236)
      | v2_struct_0(B_236)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_215,plain,(
    ! [D_238] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_238)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_238)
      | ~ m1_pre_topc(D_238,'#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_209])).

tff(c_226,plain,(
    ! [D_238] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_238)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_238)
      | ~ m1_pre_topc(D_238,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_48,c_46,c_215])).

tff(c_227,plain,(
    ! [D_238] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_238)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_238)
      | ~ m1_pre_topc(D_238,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_226])).

tff(c_248,plain,(
    ! [D_238] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_238)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_238)
      | ~ m1_pre_topc(D_238,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_208,c_227])).

tff(c_301,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_248])).

tff(c_308,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_301])).

tff(c_313,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_146])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_313])).

tff(c_317,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_386,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_317])).

tff(c_428,plain,(
    ! [C_278,A_276,B_277,E_280,D_279] :
      ( k3_tmap_1(A_276,B_277,C_278,D_279,E_280) = k2_partfun1(u1_struct_0(C_278),u1_struct_0(B_277),E_280,u1_struct_0(D_279))
      | ~ m1_pre_topc(D_279,C_278)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278),u1_struct_0(B_277))))
      | ~ v1_funct_2(E_280,u1_struct_0(C_278),u1_struct_0(B_277))
      | ~ v1_funct_1(E_280)
      | ~ m1_pre_topc(D_279,A_276)
      | ~ m1_pre_topc(C_278,A_276)
      | ~ l1_pre_topc(B_277)
      | ~ v2_pre_topc(B_277)
      | v2_struct_0(B_277)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_430,plain,(
    ! [A_276,D_279] :
      ( k3_tmap_1(A_276,'#skF_3','#skF_2',D_279,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_279))
      | ~ m1_pre_topc(D_279,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_279,A_276)
      | ~ m1_pre_topc('#skF_2',A_276)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(resolution,[status(thm)],[c_82,c_428])).

tff(c_435,plain,(
    ! [A_276,D_279] :
      ( k3_tmap_1(A_276,'#skF_3','#skF_2',D_279,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_279))
      | ~ m1_pre_topc(D_279,'#skF_2')
      | ~ m1_pre_topc(D_279,A_276)
      | ~ m1_pre_topc('#skF_2',A_276)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_430])).

tff(c_441,plain,(
    ! [A_281,D_282] :
      ( k3_tmap_1(A_281,'#skF_3','#skF_2',D_282,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_282))
      | ~ m1_pre_topc(D_282,'#skF_2')
      | ~ m1_pre_topc(D_282,A_281)
      | ~ m1_pre_topc('#skF_2',A_281)
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_435])).

tff(c_443,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_441])).

tff(c_448,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_443])).

tff(c_449,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_448])).

tff(c_405,plain,(
    ! [A_271,B_272,C_273,D_274] :
      ( k2_partfun1(u1_struct_0(A_271),u1_struct_0(B_272),C_273,u1_struct_0(D_274)) = k2_tmap_1(A_271,B_272,C_273,D_274)
      | ~ m1_pre_topc(D_274,A_271)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_271),u1_struct_0(B_272))))
      | ~ v1_funct_2(C_273,u1_struct_0(A_271),u1_struct_0(B_272))
      | ~ v1_funct_1(C_273)
      | ~ l1_pre_topc(B_272)
      | ~ v2_pre_topc(B_272)
      | v2_struct_0(B_272)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_407,plain,(
    ! [D_274] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_274)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_274)
      | ~ m1_pre_topc(D_274,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_82,c_405])).

tff(c_412,plain,(
    ! [D_274] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_274)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_274)
      | ~ m1_pre_topc(D_274,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_36,c_81,c_407])).

tff(c_413,plain,(
    ! [D_274] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_274)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_274)
      | ~ m1_pre_topc(D_274,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_412])).

tff(c_457,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_413])).

tff(c_464,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_457])).

tff(c_326,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_326])).

tff(c_328,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_469,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_328])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_469])).

tff(c_473,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_119,plain,(
    ! [A_206] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_206,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_500,plain,(
    ! [A_286] : ~ r2_hidden(A_286,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_119])).

tff(c_506,plain,(
    ! [B_287] : r1_tarski('#skF_6',B_287) ),
    inference(resolution,[status(thm)],[c_6,c_500])).

tff(c_474,plain,(
    ! [A_283] : ~ r2_hidden(A_283,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_480,plain,(
    ! [B_284] : r1_tarski('#skF_8',B_284) ),
    inference(resolution,[status(thm)],[c_6,c_474])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_483,plain,(
    ! [B_284] :
      ( B_284 = '#skF_8'
      | ~ r1_tarski(B_284,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_480,c_8])).

tff(c_513,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_506,c_483])).

tff(c_573,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_80])).

tff(c_574,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_582,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_78])).

tff(c_583,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_582])).

tff(c_644,plain,(
    ! [C_323,D_324,B_322,E_325,A_321] :
      ( k3_tmap_1(A_321,B_322,C_323,D_324,E_325) = k2_partfun1(u1_struct_0(C_323),u1_struct_0(B_322),E_325,u1_struct_0(D_324))
      | ~ m1_pre_topc(D_324,C_323)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323),u1_struct_0(B_322))))
      | ~ v1_funct_2(E_325,u1_struct_0(C_323),u1_struct_0(B_322))
      | ~ v1_funct_1(E_325)
      | ~ m1_pre_topc(D_324,A_321)
      | ~ m1_pre_topc(C_323,A_321)
      | ~ l1_pre_topc(B_322)
      | ~ v2_pre_topc(B_322)
      | v2_struct_0(B_322)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_646,plain,(
    ! [A_321,D_324] :
      ( k3_tmap_1(A_321,'#skF_3','#skF_2',D_324,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_324))
      | ~ m1_pre_topc(D_324,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_324,A_321)
      | ~ m1_pre_topc('#skF_2',A_321)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_82,c_644])).

tff(c_651,plain,(
    ! [A_321,D_324] :
      ( k3_tmap_1(A_321,'#skF_3','#skF_2',D_324,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_324))
      | ~ m1_pre_topc(D_324,'#skF_2')
      | ~ m1_pre_topc(D_324,A_321)
      | ~ m1_pre_topc('#skF_2',A_321)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_646])).

tff(c_657,plain,(
    ! [A_326,D_327] :
      ( k3_tmap_1(A_326,'#skF_3','#skF_2',D_327,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_327))
      | ~ m1_pre_topc(D_327,'#skF_2')
      | ~ m1_pre_topc(D_327,A_326)
      | ~ m1_pre_topc('#skF_2',A_326)
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_651])).

tff(c_659,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_657])).

tff(c_664,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_659])).

tff(c_665,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_664])).

tff(c_621,plain,(
    ! [A_316,B_317,C_318,D_319] :
      ( k2_partfun1(u1_struct_0(A_316),u1_struct_0(B_317),C_318,u1_struct_0(D_319)) = k2_tmap_1(A_316,B_317,C_318,D_319)
      | ~ m1_pre_topc(D_319,A_316)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_316),u1_struct_0(B_317))))
      | ~ v1_funct_2(C_318,u1_struct_0(A_316),u1_struct_0(B_317))
      | ~ v1_funct_1(C_318)
      | ~ l1_pre_topc(B_317)
      | ~ v2_pre_topc(B_317)
      | v2_struct_0(B_317)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_623,plain,(
    ! [D_319] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_319)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_319)
      | ~ m1_pre_topc(D_319,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_82,c_621])).

tff(c_628,plain,(
    ! [D_319] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_319)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_319)
      | ~ m1_pre_topc(D_319,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_36,c_81,c_623])).

tff(c_629,plain,(
    ! [D_319] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_319)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_319)
      | ~ m1_pre_topc(D_319,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_628])).

tff(c_673,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_629])).

tff(c_680,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_673])).

tff(c_698,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_574])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_698])).

tff(c_702,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_774,plain,(
    ! [C_356,D_357,B_355,E_358,A_354] :
      ( k3_tmap_1(A_354,B_355,C_356,D_357,E_358) = k2_partfun1(u1_struct_0(C_356),u1_struct_0(B_355),E_358,u1_struct_0(D_357))
      | ~ m1_pre_topc(D_357,C_356)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_356),u1_struct_0(B_355))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_356),u1_struct_0(B_355))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc(D_357,A_354)
      | ~ m1_pre_topc(C_356,A_354)
      | ~ l1_pre_topc(B_355)
      | ~ v2_pre_topc(B_355)
      | v2_struct_0(B_355)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_776,plain,(
    ! [A_354,D_357] :
      ( k3_tmap_1(A_354,'#skF_3','#skF_2',D_357,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_357))
      | ~ m1_pre_topc(D_357,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_357,A_354)
      | ~ m1_pre_topc('#skF_2',A_354)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_82,c_774])).

tff(c_781,plain,(
    ! [A_354,D_357] :
      ( k3_tmap_1(A_354,'#skF_3','#skF_2',D_357,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_357))
      | ~ m1_pre_topc(D_357,'#skF_2')
      | ~ m1_pre_topc(D_357,A_354)
      | ~ m1_pre_topc('#skF_2',A_354)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_776])).

tff(c_787,plain,(
    ! [A_359,D_360] :
      ( k3_tmap_1(A_359,'#skF_3','#skF_2',D_360,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_360))
      | ~ m1_pre_topc(D_360,'#skF_2')
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc('#skF_2',A_359)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_781])).

tff(c_789,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_787])).

tff(c_794,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_789])).

tff(c_795,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_794])).

tff(c_751,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_753,plain,(
    ! [D_352] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_352)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_352)
      | ~ m1_pre_topc(D_352,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_82,c_751])).

tff(c_758,plain,(
    ! [D_352] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_352)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_352)
      | ~ m1_pre_topc(D_352,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_36,c_81,c_753])).

tff(c_759,plain,(
    ! [D_352] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_352)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_352)
      | ~ m1_pre_topc(D_352,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_758])).

tff(c_803,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_759])).

tff(c_810,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_803])).

tff(c_704,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_78])).

tff(c_705,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_704])).

tff(c_815,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_705])).

tff(c_817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.50  
% 3.32/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.50  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.47/1.50  
% 3.47/1.50  %Foreground sorts:
% 3.47/1.50  
% 3.47/1.50  
% 3.47/1.50  %Background operators:
% 3.47/1.50  
% 3.47/1.50  
% 3.47/1.50  %Foreground operators:
% 3.47/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.47/1.50  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.47/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.47/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.47/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.50  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.47/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.47/1.50  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.47/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.47/1.50  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.47/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.50  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.47/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.50  
% 3.47/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.53  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.47/1.53  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 3.47/1.53  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.47/1.53  tff(f_71, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.47/1.53  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.47/1.53  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.47/1.53  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.53  tff(c_14, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.47/1.53  tff(c_30, plain, ('#skF_5'='#skF_2'), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_82, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.47/1.53  tff(c_110, plain, (![C_204, B_205, A_206]: (~v1_xboole_0(C_204) | ~m1_subset_1(B_205, k1_zfmisc_1(C_204)) | ~r2_hidden(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.47/1.53  tff(c_117, plain, (![A_206]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_206, '#skF_8'))), inference(resolution, [status(thm)], [c_82, c_110])).
% 3.47/1.53  tff(c_120, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_117])).
% 3.47/1.53  tff(c_124, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_120])).
% 3.47/1.53  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_46, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_36, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_34, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_81, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 3.47/1.53  tff(c_28, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_83, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 3.47/1.53  tff(c_357, plain, (![A_269, B_267, F_265, C_270, D_266, E_268]: (F_265=E_268 | ~r1_funct_2(A_269, B_267, C_270, D_266, E_268, F_265) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(C_270, D_266))) | ~v1_funct_2(F_265, C_270, D_266) | ~v1_funct_1(F_265) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_267))) | ~v1_funct_2(E_268, A_269, B_267) | ~v1_funct_1(E_268) | v1_xboole_0(D_266) | v1_xboole_0(B_267))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.53  tff(c_365, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_357])).
% 3.47/1.53  tff(c_383, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_81, c_82, c_365])).
% 3.47/1.53  tff(c_384, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_124, c_383])).
% 3.47/1.53  tff(c_181, plain, (![A_233, C_234, F_229, E_232, B_231, D_230]: (F_229=E_232 | ~r1_funct_2(A_233, B_231, C_234, D_230, E_232, F_229) | ~m1_subset_1(F_229, k1_zfmisc_1(k2_zfmisc_1(C_234, D_230))) | ~v1_funct_2(F_229, C_234, D_230) | ~v1_funct_1(F_229) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_231))) | ~v1_funct_2(E_232, A_233, B_231) | ~v1_funct_1(E_232) | v1_xboole_0(D_230) | v1_xboole_0(B_231))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.53  tff(c_189, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_181])).
% 3.47/1.53  tff(c_207, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_81, c_82, c_189])).
% 3.47/1.53  tff(c_208, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_124, c_207])).
% 3.47/1.53  tff(c_70, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_80, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_70])).
% 3.47/1.53  tff(c_146, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_80])).
% 3.47/1.53  tff(c_76, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_78, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_76])).
% 3.47/1.53  tff(c_158, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_78])).
% 3.47/1.53  tff(c_229, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_158])).
% 3.47/1.53  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_79, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_50])).
% 3.47/1.53  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.47/1.53  tff(c_259, plain, (![E_244, D_243, C_242, A_240, B_241]: (k3_tmap_1(A_240, B_241, C_242, D_243, E_244)=k2_partfun1(u1_struct_0(C_242), u1_struct_0(B_241), E_244, u1_struct_0(D_243)) | ~m1_pre_topc(D_243, C_242) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_242), u1_struct_0(B_241)))) | ~v1_funct_2(E_244, u1_struct_0(C_242), u1_struct_0(B_241)) | ~v1_funct_1(E_244) | ~m1_pre_topc(D_243, A_240) | ~m1_pre_topc(C_242, A_240) | ~l1_pre_topc(B_241) | ~v2_pre_topc(B_241) | v2_struct_0(B_241) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.47/1.53  tff(c_261, plain, (![A_240, D_243]: (k3_tmap_1(A_240, '#skF_3', '#skF_2', D_243, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_243)) | ~m1_pre_topc(D_243, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_243, A_240) | ~m1_pre_topc('#skF_2', A_240) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(resolution, [status(thm)], [c_82, c_259])).
% 3.47/1.53  tff(c_266, plain, (![A_240, D_243]: (k3_tmap_1(A_240, '#skF_3', '#skF_2', D_243, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_243)) | ~m1_pre_topc(D_243, '#skF_2') | ~m1_pre_topc(D_243, A_240) | ~m1_pre_topc('#skF_2', A_240) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_261])).
% 3.47/1.53  tff(c_272, plain, (![A_245, D_246]: (k3_tmap_1(A_245, '#skF_3', '#skF_2', D_246, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_246)) | ~m1_pre_topc(D_246, '#skF_2') | ~m1_pre_topc(D_246, A_245) | ~m1_pre_topc('#skF_2', A_245) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(negUnitSimplification, [status(thm)], [c_62, c_266])).
% 3.47/1.53  tff(c_274, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_272])).
% 3.47/1.53  tff(c_279, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_274])).
% 3.47/1.53  tff(c_280, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_279])).
% 3.47/1.53  tff(c_209, plain, (![A_235, B_236, C_237, D_238]: (k2_partfun1(u1_struct_0(A_235), u1_struct_0(B_236), C_237, u1_struct_0(D_238))=k2_tmap_1(A_235, B_236, C_237, D_238) | ~m1_pre_topc(D_238, A_235) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), u1_struct_0(B_236)))) | ~v1_funct_2(C_237, u1_struct_0(A_235), u1_struct_0(B_236)) | ~v1_funct_1(C_237) | ~l1_pre_topc(B_236) | ~v2_pre_topc(B_236) | v2_struct_0(B_236) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.47/1.53  tff(c_215, plain, (![D_238]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_238))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_238) | ~m1_pre_topc(D_238, '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_209])).
% 3.47/1.53  tff(c_226, plain, (![D_238]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_238))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_238) | ~m1_pre_topc(D_238, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_48, c_46, c_215])).
% 3.47/1.53  tff(c_227, plain, (![D_238]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_238))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_238) | ~m1_pre_topc(D_238, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_226])).
% 3.47/1.53  tff(c_248, plain, (![D_238]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_238))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_238) | ~m1_pre_topc(D_238, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_208, c_227])).
% 3.47/1.53  tff(c_301, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_280, c_248])).
% 3.47/1.53  tff(c_308, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_301])).
% 3.47/1.53  tff(c_313, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_146])).
% 3.47/1.53  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_313])).
% 3.47/1.53  tff(c_317, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 3.47/1.53  tff(c_386, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_317])).
% 3.47/1.53  tff(c_428, plain, (![C_278, A_276, B_277, E_280, D_279]: (k3_tmap_1(A_276, B_277, C_278, D_279, E_280)=k2_partfun1(u1_struct_0(C_278), u1_struct_0(B_277), E_280, u1_struct_0(D_279)) | ~m1_pre_topc(D_279, C_278) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278), u1_struct_0(B_277)))) | ~v1_funct_2(E_280, u1_struct_0(C_278), u1_struct_0(B_277)) | ~v1_funct_1(E_280) | ~m1_pre_topc(D_279, A_276) | ~m1_pre_topc(C_278, A_276) | ~l1_pre_topc(B_277) | ~v2_pre_topc(B_277) | v2_struct_0(B_277) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.47/1.53  tff(c_430, plain, (![A_276, D_279]: (k3_tmap_1(A_276, '#skF_3', '#skF_2', D_279, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_279)) | ~m1_pre_topc(D_279, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_279, A_276) | ~m1_pre_topc('#skF_2', A_276) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(resolution, [status(thm)], [c_82, c_428])).
% 3.47/1.53  tff(c_435, plain, (![A_276, D_279]: (k3_tmap_1(A_276, '#skF_3', '#skF_2', D_279, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_279)) | ~m1_pre_topc(D_279, '#skF_2') | ~m1_pre_topc(D_279, A_276) | ~m1_pre_topc('#skF_2', A_276) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_430])).
% 3.47/1.53  tff(c_441, plain, (![A_281, D_282]: (k3_tmap_1(A_281, '#skF_3', '#skF_2', D_282, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_282)) | ~m1_pre_topc(D_282, '#skF_2') | ~m1_pre_topc(D_282, A_281) | ~m1_pre_topc('#skF_2', A_281) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(negUnitSimplification, [status(thm)], [c_62, c_435])).
% 3.47/1.53  tff(c_443, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_441])).
% 3.47/1.53  tff(c_448, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_443])).
% 3.47/1.53  tff(c_449, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_448])).
% 3.47/1.53  tff(c_405, plain, (![A_271, B_272, C_273, D_274]: (k2_partfun1(u1_struct_0(A_271), u1_struct_0(B_272), C_273, u1_struct_0(D_274))=k2_tmap_1(A_271, B_272, C_273, D_274) | ~m1_pre_topc(D_274, A_271) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_271), u1_struct_0(B_272)))) | ~v1_funct_2(C_273, u1_struct_0(A_271), u1_struct_0(B_272)) | ~v1_funct_1(C_273) | ~l1_pre_topc(B_272) | ~v2_pre_topc(B_272) | v2_struct_0(B_272) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.47/1.53  tff(c_407, plain, (![D_274]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_274))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_274) | ~m1_pre_topc(D_274, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_405])).
% 3.47/1.53  tff(c_412, plain, (![D_274]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_274))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_274) | ~m1_pre_topc(D_274, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_36, c_81, c_407])).
% 3.47/1.53  tff(c_413, plain, (![D_274]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_274))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_274) | ~m1_pre_topc(D_274, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_412])).
% 3.47/1.53  tff(c_457, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_449, c_413])).
% 3.47/1.53  tff(c_464, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_457])).
% 3.47/1.53  tff(c_326, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitLeft, [status(thm)], [c_78])).
% 3.47/1.53  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_326])).
% 3.47/1.53  tff(c_328, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 3.47/1.53  tff(c_469, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_328])).
% 3.47/1.53  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_469])).
% 3.47/1.53  tff(c_473, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_117])).
% 3.47/1.53  tff(c_119, plain, (![A_206]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_206, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_110])).
% 3.47/1.53  tff(c_500, plain, (![A_286]: (~r2_hidden(A_286, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_119])).
% 3.47/1.53  tff(c_506, plain, (![B_287]: (r1_tarski('#skF_6', B_287))), inference(resolution, [status(thm)], [c_6, c_500])).
% 3.47/1.53  tff(c_474, plain, (![A_283]: (~r2_hidden(A_283, '#skF_8'))), inference(splitRight, [status(thm)], [c_117])).
% 3.47/1.53  tff(c_480, plain, (![B_284]: (r1_tarski('#skF_8', B_284))), inference(resolution, [status(thm)], [c_6, c_474])).
% 3.47/1.53  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.53  tff(c_483, plain, (![B_284]: (B_284='#skF_8' | ~r1_tarski(B_284, '#skF_8'))), inference(resolution, [status(thm)], [c_480, c_8])).
% 3.47/1.53  tff(c_513, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_506, c_483])).
% 3.47/1.53  tff(c_573, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_80])).
% 3.47/1.53  tff(c_574, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_573])).
% 3.47/1.53  tff(c_582, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_78])).
% 3.47/1.53  tff(c_583, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_574, c_582])).
% 3.47/1.53  tff(c_644, plain, (![C_323, D_324, B_322, E_325, A_321]: (k3_tmap_1(A_321, B_322, C_323, D_324, E_325)=k2_partfun1(u1_struct_0(C_323), u1_struct_0(B_322), E_325, u1_struct_0(D_324)) | ~m1_pre_topc(D_324, C_323) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323), u1_struct_0(B_322)))) | ~v1_funct_2(E_325, u1_struct_0(C_323), u1_struct_0(B_322)) | ~v1_funct_1(E_325) | ~m1_pre_topc(D_324, A_321) | ~m1_pre_topc(C_323, A_321) | ~l1_pre_topc(B_322) | ~v2_pre_topc(B_322) | v2_struct_0(B_322) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.47/1.53  tff(c_646, plain, (![A_321, D_324]: (k3_tmap_1(A_321, '#skF_3', '#skF_2', D_324, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_324)) | ~m1_pre_topc(D_324, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_324, A_321) | ~m1_pre_topc('#skF_2', A_321) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_82, c_644])).
% 3.47/1.53  tff(c_651, plain, (![A_321, D_324]: (k3_tmap_1(A_321, '#skF_3', '#skF_2', D_324, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_324)) | ~m1_pre_topc(D_324, '#skF_2') | ~m1_pre_topc(D_324, A_321) | ~m1_pre_topc('#skF_2', A_321) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_646])).
% 3.47/1.53  tff(c_657, plain, (![A_326, D_327]: (k3_tmap_1(A_326, '#skF_3', '#skF_2', D_327, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_327)) | ~m1_pre_topc(D_327, '#skF_2') | ~m1_pre_topc(D_327, A_326) | ~m1_pre_topc('#skF_2', A_326) | ~l1_pre_topc(A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326))), inference(negUnitSimplification, [status(thm)], [c_62, c_651])).
% 3.47/1.53  tff(c_659, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_657])).
% 3.47/1.53  tff(c_664, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_659])).
% 3.47/1.53  tff(c_665, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_664])).
% 3.47/1.53  tff(c_621, plain, (![A_316, B_317, C_318, D_319]: (k2_partfun1(u1_struct_0(A_316), u1_struct_0(B_317), C_318, u1_struct_0(D_319))=k2_tmap_1(A_316, B_317, C_318, D_319) | ~m1_pre_topc(D_319, A_316) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_316), u1_struct_0(B_317)))) | ~v1_funct_2(C_318, u1_struct_0(A_316), u1_struct_0(B_317)) | ~v1_funct_1(C_318) | ~l1_pre_topc(B_317) | ~v2_pre_topc(B_317) | v2_struct_0(B_317) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.47/1.53  tff(c_623, plain, (![D_319]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_319))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_319) | ~m1_pre_topc(D_319, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_621])).
% 3.47/1.53  tff(c_628, plain, (![D_319]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_319))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_319) | ~m1_pre_topc(D_319, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_36, c_81, c_623])).
% 3.47/1.53  tff(c_629, plain, (![D_319]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_319))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_319) | ~m1_pre_topc(D_319, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_628])).
% 3.47/1.53  tff(c_673, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_665, c_629])).
% 3.47/1.53  tff(c_680, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_673])).
% 3.47/1.53  tff(c_698, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_680, c_574])).
% 3.47/1.53  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_583, c_698])).
% 3.47/1.53  tff(c_702, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_573])).
% 3.47/1.53  tff(c_774, plain, (![C_356, D_357, B_355, E_358, A_354]: (k3_tmap_1(A_354, B_355, C_356, D_357, E_358)=k2_partfun1(u1_struct_0(C_356), u1_struct_0(B_355), E_358, u1_struct_0(D_357)) | ~m1_pre_topc(D_357, C_356) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_356), u1_struct_0(B_355)))) | ~v1_funct_2(E_358, u1_struct_0(C_356), u1_struct_0(B_355)) | ~v1_funct_1(E_358) | ~m1_pre_topc(D_357, A_354) | ~m1_pre_topc(C_356, A_354) | ~l1_pre_topc(B_355) | ~v2_pre_topc(B_355) | v2_struct_0(B_355) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.47/1.53  tff(c_776, plain, (![A_354, D_357]: (k3_tmap_1(A_354, '#skF_3', '#skF_2', D_357, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_357)) | ~m1_pre_topc(D_357, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_357, A_354) | ~m1_pre_topc('#skF_2', A_354) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(resolution, [status(thm)], [c_82, c_774])).
% 3.47/1.53  tff(c_781, plain, (![A_354, D_357]: (k3_tmap_1(A_354, '#skF_3', '#skF_2', D_357, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_357)) | ~m1_pre_topc(D_357, '#skF_2') | ~m1_pre_topc(D_357, A_354) | ~m1_pre_topc('#skF_2', A_354) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_776])).
% 3.47/1.53  tff(c_787, plain, (![A_359, D_360]: (k3_tmap_1(A_359, '#skF_3', '#skF_2', D_360, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_360)) | ~m1_pre_topc(D_360, '#skF_2') | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc('#skF_2', A_359) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(negUnitSimplification, [status(thm)], [c_62, c_781])).
% 3.47/1.53  tff(c_789, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_787])).
% 3.47/1.53  tff(c_794, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_789])).
% 3.47/1.53  tff(c_795, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_794])).
% 3.47/1.53  tff(c_751, plain, (![A_349, B_350, C_351, D_352]: (k2_partfun1(u1_struct_0(A_349), u1_struct_0(B_350), C_351, u1_struct_0(D_352))=k2_tmap_1(A_349, B_350, C_351, D_352) | ~m1_pre_topc(D_352, A_349) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_349), u1_struct_0(B_350)))) | ~v1_funct_2(C_351, u1_struct_0(A_349), u1_struct_0(B_350)) | ~v1_funct_1(C_351) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.47/1.53  tff(c_753, plain, (![D_352]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_352))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_352) | ~m1_pre_topc(D_352, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_751])).
% 3.47/1.53  tff(c_758, plain, (![D_352]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_352))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_352) | ~m1_pre_topc(D_352, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_36, c_81, c_753])).
% 3.47/1.53  tff(c_759, plain, (![D_352]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_352))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_352) | ~m1_pre_topc(D_352, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_758])).
% 3.47/1.53  tff(c_803, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_795, c_759])).
% 3.47/1.53  tff(c_810, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_803])).
% 3.47/1.53  tff(c_704, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_78])).
% 3.47/1.53  tff(c_705, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_702, c_704])).
% 3.47/1.53  tff(c_815, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_810, c_705])).
% 3.47/1.53  tff(c_817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_702, c_815])).
% 3.47/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.53  
% 3.47/1.53  Inference rules
% 3.47/1.53  ----------------------
% 3.47/1.53  #Ref     : 0
% 3.47/1.53  #Sup     : 123
% 3.47/1.53  #Fact    : 0
% 3.47/1.53  #Define  : 0
% 3.47/1.53  #Split   : 10
% 3.47/1.53  #Chain   : 0
% 3.47/1.53  #Close   : 0
% 3.47/1.53  
% 3.47/1.53  Ordering : KBO
% 3.47/1.53  
% 3.47/1.53  Simplification rules
% 3.47/1.53  ----------------------
% 3.47/1.53  #Subsume      : 15
% 3.47/1.53  #Demod        : 275
% 3.47/1.53  #Tautology    : 66
% 3.47/1.53  #SimpNegUnit  : 61
% 3.47/1.53  #BackRed      : 26
% 3.47/1.53  
% 3.47/1.53  #Partial instantiations: 0
% 3.47/1.53  #Strategies tried      : 1
% 3.47/1.53  
% 3.47/1.53  Timing (in seconds)
% 3.47/1.53  ----------------------
% 3.47/1.53  Preprocessing        : 0.36
% 3.47/1.53  Parsing              : 0.18
% 3.47/1.53  CNF conversion       : 0.05
% 3.47/1.53  Main loop            : 0.38
% 3.47/1.53  Inferencing          : 0.13
% 3.47/1.53  Reduction            : 0.14
% 3.47/1.53  Demodulation         : 0.10
% 3.47/1.53  BG Simplification    : 0.02
% 3.47/1.53  Subsumption          : 0.06
% 3.47/1.53  Abstraction          : 0.02
% 3.47/1.53  MUC search           : 0.00
% 3.47/1.53  Cooper               : 0.00
% 3.47/1.53  Total                : 0.80
% 3.47/1.53  Index Insertion      : 0.00
% 3.47/1.53  Index Deletion       : 0.00
% 3.47/1.53  Index Matching       : 0.00
% 3.47/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
