%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 923 expanded)
%              Number of leaves         :   40 ( 353 expanded)
%              Depth                    :   18
%              Number of atoms          :  496 (8193 expanded)
%              Number of equality atoms :   49 ( 556 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => ( ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(D))
                                   => ( r2_hidden(G,u1_struct_0(C))
                                     => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,G) = k1_funct_1(F,G) ) )
                               => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_141,axiom,(
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

tff(f_159,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_38,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_134,plain,(
    ! [A_248,B_249,D_250] :
      ( r2_funct_2(A_248,B_249,D_250,D_250)
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ v1_funct_2(D_250,A_248,B_249)
      | ~ v1_funct_1(D_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_134])).

tff(c_148,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_141])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_82,plain,(
    ! [B_244,A_245] :
      ( l1_pre_topc(B_244)
      | ~ m1_pre_topc(B_244,A_245)
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_98,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88])).

tff(c_18,plain,(
    ! [A_72] :
      ( l1_struct_0(A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_46,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_218,plain,(
    ! [C_271,D_274,E_270,A_273,B_272] :
      ( r2_hidden('#skF_1'(E_270,C_271,B_272,A_273,D_274),D_274)
      | k2_partfun1(A_273,B_272,C_271,D_274) = E_270
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(D_274,B_272)))
      | ~ v1_funct_2(E_270,D_274,B_272)
      | ~ v1_funct_1(E_270)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(A_273))
      | v1_xboole_0(D_274)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,B_272)))
      | ~ v1_funct_2(C_271,A_273,B_272)
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(B_272)
      | v1_xboole_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_220,plain,(
    ! [C_271,A_273] :
      ( r2_hidden('#skF_1'('#skF_6',C_271,u1_struct_0('#skF_3'),A_273,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_271,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_273))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_271,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_228,plain,(
    ! [C_271,A_273] :
      ( r2_hidden('#skF_1'('#skF_6',C_271,u1_struct_0('#skF_3'),A_273,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_271,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_273))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_271,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_220])).

tff(c_233,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_22,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(u1_struct_0(A_76))
      | ~ l1_struct_0(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_236,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_22])).

tff(c_239,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_236])).

tff(c_242,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_239])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_242])).

tff(c_247,plain,(
    ! [C_271,A_273] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | r2_hidden('#skF_1'('#skF_6',C_271,u1_struct_0('#skF_3'),A_273,u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_271,u1_struct_0('#skF_5')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_273))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_271,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(A_273) ) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_286,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_289,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_286,c_22])).

tff(c_292,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_289])).

tff(c_295,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_292])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_295])).

tff(c_301,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_109,plain,(
    ! [B_246,A_247] :
      ( v2_pre_topc(B_246)
      | ~ m1_pre_topc(B_246,A_247)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_115,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_125,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_115])).

tff(c_26,plain,(
    ! [A_108] :
      ( m1_pre_topc(A_108,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_437,plain,(
    ! [B_317,C_316,D_314,E_315,A_313] :
      ( k3_tmap_1(A_313,B_317,C_316,D_314,E_315) = k2_partfun1(u1_struct_0(C_316),u1_struct_0(B_317),E_315,u1_struct_0(D_314))
      | ~ m1_pre_topc(D_314,C_316)
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_316),u1_struct_0(B_317))))
      | ~ v1_funct_2(E_315,u1_struct_0(C_316),u1_struct_0(B_317))
      | ~ v1_funct_1(E_315)
      | ~ m1_pre_topc(D_314,A_313)
      | ~ m1_pre_topc(C_316,A_313)
      | ~ l1_pre_topc(B_317)
      | ~ v2_pre_topc(B_317)
      | v2_struct_0(B_317)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_448,plain,(
    ! [A_313,D_314] :
      ( k3_tmap_1(A_313,'#skF_3','#skF_5',D_314,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_314))
      | ~ m1_pre_topc(D_314,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_314,A_313)
      | ~ m1_pre_topc('#skF_5',A_313)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(resolution,[status(thm)],[c_44,c_437])).

tff(c_459,plain,(
    ! [A_313,D_314] :
      ( k3_tmap_1(A_313,'#skF_3','#skF_5',D_314,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_314))
      | ~ m1_pre_topc(D_314,'#skF_5')
      | ~ m1_pre_topc(D_314,A_313)
      | ~ m1_pre_topc('#skF_5',A_313)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_448])).

tff(c_466,plain,(
    ! [A_318,D_319] :
      ( k3_tmap_1(A_318,'#skF_3','#skF_5',D_319,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_319))
      | ~ m1_pre_topc(D_319,'#skF_5')
      | ~ m1_pre_topc(D_319,A_318)
      | ~ m1_pre_topc('#skF_5',A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_459])).

tff(c_470,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_466])).

tff(c_478,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_470])).

tff(c_479,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_478])).

tff(c_492,plain,(
    ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_497,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_492])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_497])).

tff(c_503,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_28,plain,(
    ! [B_113,C_115,A_109] :
      ( r1_tarski(u1_struct_0(B_113),u1_struct_0(C_115))
      | ~ m1_pre_topc(B_113,C_115)
      | ~ m1_pre_topc(C_115,A_109)
      | ~ m1_pre_topc(B_113,A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_507,plain,(
    ! [B_113] :
      ( r1_tarski(u1_struct_0(B_113),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_113,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_503,c_28])).

tff(c_520,plain,(
    ! [B_113] :
      ( r1_tarski(u1_struct_0(B_113),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_113,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_98,c_507])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_248,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_82])).

tff(c_102,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_94])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_225,plain,(
    ! [C_271,A_273] :
      ( r2_hidden('#skF_1'('#skF_7',C_271,u1_struct_0('#skF_3'),A_273,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_271,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_273))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_271,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_232,plain,(
    ! [C_271,A_273] :
      ( r2_hidden('#skF_1'('#skF_7',C_271,u1_struct_0('#skF_3'),A_273,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_271,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_273))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_271,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_225])).

tff(c_249,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_249])).

tff(c_251,plain,(
    ! [C_271,A_273] :
      ( v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_hidden('#skF_1'('#skF_7',C_271,u1_struct_0('#skF_3'),A_273,u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_271,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_273))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_271,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_271)
      | v1_xboole_0(A_273) ) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_253,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_273,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_253,c_22])).

tff(c_276,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_273])).

tff(c_279,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_276])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_279])).

tff(c_285,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_76,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_474,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_466])).

tff(c_486,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_42,c_474])).

tff(c_487,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_486])).

tff(c_634,plain,(
    ! [C_331,A_330,D_333,B_329,A_332] :
      ( r2_hidden('#skF_1'(A_332,C_331,B_329,A_330,D_333),D_333)
      | k2_partfun1(A_330,B_329,C_331,D_333) = A_332
      | ~ v1_funct_2(A_332,D_333,B_329)
      | ~ v1_funct_1(A_332)
      | ~ m1_subset_1(D_333,k1_zfmisc_1(A_330))
      | v1_xboole_0(D_333)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329)))
      | ~ v1_funct_2(C_331,A_330,B_329)
      | ~ v1_funct_1(C_331)
      | v1_xboole_0(B_329)
      | v1_xboole_0(A_330)
      | ~ r1_tarski(A_332,k2_zfmisc_1(D_333,B_329)) ) ),
    inference(resolution,[status(thm)],[c_4,c_218])).

tff(c_658,plain,(
    ! [A_330,A_1,D_333,B_329,A_332] :
      ( r2_hidden('#skF_1'(A_332,A_1,B_329,A_330,D_333),D_333)
      | k2_partfun1(A_330,B_329,A_1,D_333) = A_332
      | ~ v1_funct_2(A_332,D_333,B_329)
      | ~ v1_funct_1(A_332)
      | ~ m1_subset_1(D_333,k1_zfmisc_1(A_330))
      | v1_xboole_0(D_333)
      | ~ v1_funct_2(A_1,A_330,B_329)
      | ~ v1_funct_1(A_1)
      | v1_xboole_0(B_329)
      | v1_xboole_0(A_330)
      | ~ r1_tarski(A_332,k2_zfmisc_1(D_333,B_329))
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_330,B_329)) ) ),
    inference(resolution,[status(thm)],[c_4,c_634])).

tff(c_34,plain,(
    ! [G_236] :
      ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',G_236) = k1_funct_1('#skF_7',G_236)
      | ~ r2_hidden(G_236,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_236,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_540,plain,(
    ! [B_323,C_322,D_325,E_321,A_324] :
      ( k3_funct_2(A_324,B_323,C_322,'#skF_1'(E_321,C_322,B_323,A_324,D_325)) != k1_funct_1(E_321,'#skF_1'(E_321,C_322,B_323,A_324,D_325))
      | k2_partfun1(A_324,B_323,C_322,D_325) = E_321
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(D_325,B_323)))
      | ~ v1_funct_2(E_321,D_325,B_323)
      | ~ v1_funct_1(E_321)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(A_324))
      | v1_xboole_0(D_325)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_324,B_323)))
      | ~ v1_funct_2(C_322,A_324,B_323)
      | ~ v1_funct_1(C_322)
      | v1_xboole_0(B_323)
      | v1_xboole_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_543,plain,(
    ! [E_321,D_325] :
      ( k1_funct_1(E_321,'#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325)) != k1_funct_1('#skF_7','#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_325) = E_321
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(D_325,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_321,D_325,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_321)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_325)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_540])).

tff(c_545,plain,(
    ! [E_321,D_325] :
      ( k1_funct_1(E_321,'#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325)) != k1_funct_1('#skF_7','#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_325) = E_321
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(D_325,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_321,D_325,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_321)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_325)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_543])).

tff(c_546,plain,(
    ! [E_321,D_325] :
      ( k1_funct_1(E_321,'#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325)) != k1_funct_1('#skF_7','#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325))
      | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_325) = E_321
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(D_325,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_321,D_325,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_321)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_325)
      | ~ r2_hidden('#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(E_321,'#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_248,c_545])).

tff(c_1008,plain,(
    ! [D_325] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_325) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_325,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_325,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_325,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_325)
      | ~ r2_hidden('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_325),u1_struct_0('#skF_5')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_546])).

tff(c_1041,plain,(
    ! [D_377] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_377) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_377,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_377,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_377,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0(D_377)
      | ~ r2_hidden('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_377),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),D_377),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1008])).

tff(c_1045,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')),u1_struct_0('#skF_5'))
    | k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ r1_tarski('#skF_7',k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | ~ r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_658,c_1041])).

tff(c_1056,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_76,c_48,c_46,c_40,c_38,c_487,c_36,c_1045])).

tff(c_1057,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_248,c_285,c_1056])).

tff(c_1066,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1057])).

tff(c_1079,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_1066])).

tff(c_1082,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_520,c_1079])).

tff(c_1089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1082])).

tff(c_1091,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1057])).

tff(c_304,plain,(
    ! [B_286,D_288,C_285,A_287,E_284] :
      ( m1_subset_1('#skF_1'(E_284,C_285,B_286,A_287,D_288),A_287)
      | k2_partfun1(A_287,B_286,C_285,D_288) = E_284
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(D_288,B_286)))
      | ~ v1_funct_2(E_284,D_288,B_286)
      | ~ v1_funct_1(E_284)
      | ~ m1_subset_1(D_288,k1_zfmisc_1(A_287))
      | v1_xboole_0(D_288)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_286)))
      | ~ v1_funct_2(C_285,A_287,B_286)
      | ~ v1_funct_1(C_285)
      | v1_xboole_0(B_286)
      | v1_xboole_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_367,plain,(
    ! [A_300,A_301,D_297,B_299,C_298] :
      ( m1_subset_1('#skF_1'(A_301,C_298,B_299,A_300,D_297),A_300)
      | k2_partfun1(A_300,B_299,C_298,D_297) = A_301
      | ~ v1_funct_2(A_301,D_297,B_299)
      | ~ v1_funct_1(A_301)
      | ~ m1_subset_1(D_297,k1_zfmisc_1(A_300))
      | v1_xboole_0(D_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_300,B_299)))
      | ~ v1_funct_2(C_298,A_300,B_299)
      | ~ v1_funct_1(C_298)
      | v1_xboole_0(B_299)
      | v1_xboole_0(A_300)
      | ~ r1_tarski(A_301,k2_zfmisc_1(D_297,B_299)) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_394,plain,(
    ! [A_308,D_307,B_306,A_310,A_309] :
      ( m1_subset_1('#skF_1'(A_310,A_309,B_306,A_308,D_307),A_308)
      | k2_partfun1(A_308,B_306,A_309,D_307) = A_310
      | ~ v1_funct_2(A_310,D_307,B_306)
      | ~ v1_funct_1(A_310)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(A_308))
      | v1_xboole_0(D_307)
      | ~ v1_funct_2(A_309,A_308,B_306)
      | ~ v1_funct_1(A_309)
      | v1_xboole_0(B_306)
      | v1_xboole_0(A_308)
      | ~ r1_tarski(A_310,k2_zfmisc_1(D_307,B_306))
      | ~ r1_tarski(A_309,k2_zfmisc_1(A_308,B_306)) ) ),
    inference(resolution,[status(thm)],[c_4,c_367])).

tff(c_404,plain,(
    ! [A_309,A_308] :
      ( m1_subset_1('#skF_1'('#skF_7',A_309,u1_struct_0('#skF_3'),A_308,u1_struct_0('#skF_4')),A_308)
      | k2_partfun1(A_308,u1_struct_0('#skF_3'),A_309,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_308))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ v1_funct_2(A_309,A_308,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(A_309)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_308)
      | ~ r1_tarski(A_309,k2_zfmisc_1(A_308,u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_394])).

tff(c_413,plain,(
    ! [A_309,A_308] :
      ( m1_subset_1('#skF_1'('#skF_7',A_309,u1_struct_0('#skF_3'),A_308,u1_struct_0('#skF_4')),A_308)
      | k2_partfun1(A_308,u1_struct_0('#skF_3'),A_309,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_308))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ v1_funct_2(A_309,A_308,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(A_309)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_308)
      | ~ r1_tarski(A_309,k2_zfmisc_1(A_308,u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_404])).

tff(c_414,plain,(
    ! [A_309,A_308] :
      ( m1_subset_1('#skF_1'('#skF_7',A_309,u1_struct_0('#skF_3'),A_308,u1_struct_0('#skF_4')),A_308)
      | k2_partfun1(A_308,u1_struct_0('#skF_3'),A_309,u1_struct_0('#skF_4')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_308))
      | ~ v1_funct_2(A_309,A_308,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(A_309)
      | v1_xboole_0(A_308)
      | ~ r1_tarski(A_309,k2_zfmisc_1(A_308,u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_285,c_413])).

tff(c_1090,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')),u1_struct_0('#skF_5'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1057])).

tff(c_1100,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_1108,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_414,c_1100])).

tff(c_1117,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7'
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_48,c_46,c_1091,c_487,c_1108])).

tff(c_1118,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_1117])).

tff(c_32,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1129,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1118,c_32])).

tff(c_1132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1129])).

tff(c_1133,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_1137,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_32])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.86  
% 4.63/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.86  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.63/1.86  
% 4.63/1.86  %Foreground sorts:
% 4.63/1.86  
% 4.63/1.86  
% 4.63/1.86  %Background operators:
% 4.63/1.86  
% 4.63/1.86  
% 4.63/1.86  %Foreground operators:
% 4.63/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.63/1.86  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.63/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.63/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.63/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.63/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.63/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.63/1.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.63/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.63/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.86  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.63/1.86  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.63/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.86  
% 4.63/1.89  tff(f_212, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((![G]: (m1_subset_1(G, u1_struct_0(D)) => (r2_hidden(G, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, G) = k1_funct_1(F, G))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tmap_1)).
% 4.63/1.89  tff(f_45, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.63/1.89  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.63/1.89  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.63/1.89  tff(f_81, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, D, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((![F]: (m1_subset_1(F, A) => (r2_hidden(F, D) => (k3_funct_2(A, B, C, F) = k1_funct_1(E, F))))) => (k2_partfun1(A, B, C, D) = E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 4.63/1.89  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.63/1.89  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.63/1.89  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.63/1.89  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.63/1.89  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.63/1.89  tff(f_159, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.63/1.89  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_38, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_134, plain, (![A_248, B_249, D_250]: (r2_funct_2(A_248, B_249, D_250, D_250) | ~m1_subset_1(D_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~v1_funct_2(D_250, A_248, B_249) | ~v1_funct_1(D_250))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.63/1.89  tff(c_141, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_134])).
% 4.63/1.89  tff(c_148, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_141])).
% 4.63/1.89  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_82, plain, (![B_244, A_245]: (l1_pre_topc(B_244) | ~m1_pre_topc(B_244, A_245) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.63/1.89  tff(c_88, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_82])).
% 4.63/1.89  tff(c_98, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_88])).
% 4.63/1.89  tff(c_18, plain, (![A_72]: (l1_struct_0(A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.63/1.89  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_46, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_218, plain, (![C_271, D_274, E_270, A_273, B_272]: (r2_hidden('#skF_1'(E_270, C_271, B_272, A_273, D_274), D_274) | k2_partfun1(A_273, B_272, C_271, D_274)=E_270 | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(D_274, B_272))) | ~v1_funct_2(E_270, D_274, B_272) | ~v1_funct_1(E_270) | ~m1_subset_1(D_274, k1_zfmisc_1(A_273)) | v1_xboole_0(D_274) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, B_272))) | ~v1_funct_2(C_271, A_273, B_272) | ~v1_funct_1(C_271) | v1_xboole_0(B_272) | v1_xboole_0(A_273))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.89  tff(c_220, plain, (![C_271, A_273]: (r2_hidden('#skF_1'('#skF_6', C_271, u1_struct_0('#skF_3'), A_273, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | k2_partfun1(A_273, u1_struct_0('#skF_3'), C_271, u1_struct_0('#skF_5'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_273)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_271, A_273, u1_struct_0('#skF_3')) | ~v1_funct_1(C_271) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_273))), inference(resolution, [status(thm)], [c_44, c_218])).
% 4.63/1.89  tff(c_228, plain, (![C_271, A_273]: (r2_hidden('#skF_1'('#skF_6', C_271, u1_struct_0('#skF_3'), A_273, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | k2_partfun1(A_273, u1_struct_0('#skF_3'), C_271, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_273)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_271, A_273, u1_struct_0('#skF_3')) | ~v1_funct_1(C_271) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_220])).
% 4.63/1.89  tff(c_233, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_228])).
% 4.63/1.89  tff(c_22, plain, (![A_76]: (~v1_xboole_0(u1_struct_0(A_76)) | ~l1_struct_0(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.63/1.89  tff(c_236, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_233, c_22])).
% 4.63/1.89  tff(c_239, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_236])).
% 4.63/1.89  tff(c_242, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_239])).
% 4.63/1.89  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_242])).
% 4.63/1.89  tff(c_247, plain, (![C_271, A_273]: (v1_xboole_0(u1_struct_0('#skF_5')) | r2_hidden('#skF_1'('#skF_6', C_271, u1_struct_0('#skF_3'), A_273, u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | k2_partfun1(A_273, u1_struct_0('#skF_3'), C_271, u1_struct_0('#skF_5'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_273)) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_271, A_273, u1_struct_0('#skF_3')) | ~v1_funct_1(C_271) | v1_xboole_0(A_273))), inference(splitRight, [status(thm)], [c_228])).
% 4.63/1.89  tff(c_286, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_247])).
% 4.63/1.89  tff(c_289, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_286, c_22])).
% 4.63/1.89  tff(c_292, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_289])).
% 4.63/1.89  tff(c_295, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_292])).
% 4.63/1.89  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_295])).
% 4.63/1.89  tff(c_301, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_247])).
% 4.63/1.89  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.89  tff(c_108, plain, (r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_2])).
% 4.63/1.89  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_109, plain, (![B_246, A_247]: (v2_pre_topc(B_246) | ~m1_pre_topc(B_246, A_247) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.63/1.89  tff(c_115, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_109])).
% 4.63/1.89  tff(c_125, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_115])).
% 4.63/1.89  tff(c_26, plain, (![A_108]: (m1_pre_topc(A_108, A_108) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.63/1.89  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_437, plain, (![B_317, C_316, D_314, E_315, A_313]: (k3_tmap_1(A_313, B_317, C_316, D_314, E_315)=k2_partfun1(u1_struct_0(C_316), u1_struct_0(B_317), E_315, u1_struct_0(D_314)) | ~m1_pre_topc(D_314, C_316) | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_316), u1_struct_0(B_317)))) | ~v1_funct_2(E_315, u1_struct_0(C_316), u1_struct_0(B_317)) | ~v1_funct_1(E_315) | ~m1_pre_topc(D_314, A_313) | ~m1_pre_topc(C_316, A_313) | ~l1_pre_topc(B_317) | ~v2_pre_topc(B_317) | v2_struct_0(B_317) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.63/1.89  tff(c_448, plain, (![A_313, D_314]: (k3_tmap_1(A_313, '#skF_3', '#skF_5', D_314, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_314)) | ~m1_pre_topc(D_314, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_314, A_313) | ~m1_pre_topc('#skF_5', A_313) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(resolution, [status(thm)], [c_44, c_437])).
% 4.63/1.89  tff(c_459, plain, (![A_313, D_314]: (k3_tmap_1(A_313, '#skF_3', '#skF_5', D_314, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_314)) | ~m1_pre_topc(D_314, '#skF_5') | ~m1_pre_topc(D_314, A_313) | ~m1_pre_topc('#skF_5', A_313) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_448])).
% 4.63/1.89  tff(c_466, plain, (![A_318, D_319]: (k3_tmap_1(A_318, '#skF_3', '#skF_5', D_319, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_319)) | ~m1_pre_topc(D_319, '#skF_5') | ~m1_pre_topc(D_319, A_318) | ~m1_pre_topc('#skF_5', A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(negUnitSimplification, [status(thm)], [c_62, c_459])).
% 4.63/1.89  tff(c_470, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_466])).
% 4.63/1.89  tff(c_478, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_470])).
% 4.63/1.89  tff(c_479, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_478])).
% 4.63/1.89  tff(c_492, plain, (~m1_pre_topc('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_479])).
% 4.63/1.89  tff(c_497, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_26, c_492])).
% 4.63/1.89  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_497])).
% 4.63/1.89  tff(c_503, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_479])).
% 4.63/1.89  tff(c_28, plain, (![B_113, C_115, A_109]: (r1_tarski(u1_struct_0(B_113), u1_struct_0(C_115)) | ~m1_pre_topc(B_113, C_115) | ~m1_pre_topc(C_115, A_109) | ~m1_pre_topc(B_113, A_109) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.63/1.89  tff(c_507, plain, (![B_113]: (r1_tarski(u1_struct_0(B_113), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_113, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_503, c_28])).
% 4.63/1.89  tff(c_520, plain, (![B_113]: (r1_tarski(u1_struct_0(B_113), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_113, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_98, c_507])).
% 4.63/1.89  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.89  tff(c_248, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_228])).
% 4.63/1.89  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_94, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_82])).
% 4.63/1.89  tff(c_102, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_94])).
% 4.63/1.89  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_225, plain, (![C_271, A_273]: (r2_hidden('#skF_1'('#skF_7', C_271, u1_struct_0('#skF_3'), A_273, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | k2_partfun1(A_273, u1_struct_0('#skF_3'), C_271, u1_struct_0('#skF_4'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_273)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_271, A_273, u1_struct_0('#skF_3')) | ~v1_funct_1(C_271) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_273))), inference(resolution, [status(thm)], [c_36, c_218])).
% 4.63/1.89  tff(c_232, plain, (![C_271, A_273]: (r2_hidden('#skF_1'('#skF_7', C_271, u1_struct_0('#skF_3'), A_273, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | k2_partfun1(A_273, u1_struct_0('#skF_3'), C_271, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_273)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_271, A_273, u1_struct_0('#skF_3')) | ~v1_funct_1(C_271) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_225])).
% 4.63/1.89  tff(c_249, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_232])).
% 4.63/1.89  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_249])).
% 4.63/1.89  tff(c_251, plain, (![C_271, A_273]: (v1_xboole_0(u1_struct_0('#skF_4')) | r2_hidden('#skF_1'('#skF_7', C_271, u1_struct_0('#skF_3'), A_273, u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | k2_partfun1(A_273, u1_struct_0('#skF_3'), C_271, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_273)) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_273, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_271, A_273, u1_struct_0('#skF_3')) | ~v1_funct_1(C_271) | v1_xboole_0(A_273))), inference(splitRight, [status(thm)], [c_232])).
% 4.63/1.89  tff(c_253, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_251])).
% 4.63/1.89  tff(c_273, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_253, c_22])).
% 4.63/1.89  tff(c_276, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_273])).
% 4.63/1.89  tff(c_279, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_276])).
% 4.63/1.89  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_279])).
% 4.63/1.89  tff(c_285, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_251])).
% 4.63/1.89  tff(c_76, plain, (r1_tarski('#skF_7', k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_2])).
% 4.63/1.89  tff(c_474, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_466])).
% 4.63/1.89  tff(c_486, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_42, c_474])).
% 4.63/1.89  tff(c_487, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_486])).
% 4.63/1.89  tff(c_634, plain, (![C_331, A_330, D_333, B_329, A_332]: (r2_hidden('#skF_1'(A_332, C_331, B_329, A_330, D_333), D_333) | k2_partfun1(A_330, B_329, C_331, D_333)=A_332 | ~v1_funct_2(A_332, D_333, B_329) | ~v1_funct_1(A_332) | ~m1_subset_1(D_333, k1_zfmisc_1(A_330)) | v1_xboole_0(D_333) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))) | ~v1_funct_2(C_331, A_330, B_329) | ~v1_funct_1(C_331) | v1_xboole_0(B_329) | v1_xboole_0(A_330) | ~r1_tarski(A_332, k2_zfmisc_1(D_333, B_329)))), inference(resolution, [status(thm)], [c_4, c_218])).
% 4.63/1.89  tff(c_658, plain, (![A_330, A_1, D_333, B_329, A_332]: (r2_hidden('#skF_1'(A_332, A_1, B_329, A_330, D_333), D_333) | k2_partfun1(A_330, B_329, A_1, D_333)=A_332 | ~v1_funct_2(A_332, D_333, B_329) | ~v1_funct_1(A_332) | ~m1_subset_1(D_333, k1_zfmisc_1(A_330)) | v1_xboole_0(D_333) | ~v1_funct_2(A_1, A_330, B_329) | ~v1_funct_1(A_1) | v1_xboole_0(B_329) | v1_xboole_0(A_330) | ~r1_tarski(A_332, k2_zfmisc_1(D_333, B_329)) | ~r1_tarski(A_1, k2_zfmisc_1(A_330, B_329)))), inference(resolution, [status(thm)], [c_4, c_634])).
% 4.63/1.89  tff(c_34, plain, (![G_236]: (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', G_236)=k1_funct_1('#skF_7', G_236) | ~r2_hidden(G_236, u1_struct_0('#skF_4')) | ~m1_subset_1(G_236, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_540, plain, (![B_323, C_322, D_325, E_321, A_324]: (k3_funct_2(A_324, B_323, C_322, '#skF_1'(E_321, C_322, B_323, A_324, D_325))!=k1_funct_1(E_321, '#skF_1'(E_321, C_322, B_323, A_324, D_325)) | k2_partfun1(A_324, B_323, C_322, D_325)=E_321 | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(D_325, B_323))) | ~v1_funct_2(E_321, D_325, B_323) | ~v1_funct_1(E_321) | ~m1_subset_1(D_325, k1_zfmisc_1(A_324)) | v1_xboole_0(D_325) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_324, B_323))) | ~v1_funct_2(C_322, A_324, B_323) | ~v1_funct_1(C_322) | v1_xboole_0(B_323) | v1_xboole_0(A_324))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.89  tff(c_543, plain, (![E_321, D_325]: (k1_funct_1(E_321, '#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325))!=k1_funct_1('#skF_7', '#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325)) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_325)=E_321 | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(D_325, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_321, D_325, u1_struct_0('#skF_3')) | ~v1_funct_1(E_321) | ~m1_subset_1(D_325, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_325) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_540])).
% 4.63/1.89  tff(c_545, plain, (![E_321, D_325]: (k1_funct_1(E_321, '#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325))!=k1_funct_1('#skF_7', '#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325)) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_325)=E_321 | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(D_325, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_321, D_325, u1_struct_0('#skF_3')) | ~v1_funct_1(E_321) | ~m1_subset_1(D_325, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_325) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_543])).
% 4.63/1.89  tff(c_546, plain, (![E_321, D_325]: (k1_funct_1(E_321, '#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325))!=k1_funct_1('#skF_7', '#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325)) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_325)=E_321 | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(D_325, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_321, D_325, u1_struct_0('#skF_3')) | ~v1_funct_1(E_321) | ~m1_subset_1(D_325, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_325) | ~r2_hidden('#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(E_321, '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_301, c_248, c_545])).
% 4.63/1.89  tff(c_1008, plain, (![D_325]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_325)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(D_325, u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', D_325, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_325, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_325) | ~r2_hidden('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_325), u1_struct_0('#skF_5')))), inference(reflexivity, [status(thm), theory('equality')], [c_546])).
% 4.63/1.89  tff(c_1041, plain, (![D_377]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_377)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(D_377, u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', D_377, u1_struct_0('#skF_3')) | ~m1_subset_1(D_377, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(D_377) | ~r2_hidden('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_377), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), D_377), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1008])).
% 4.63/1.89  tff(c_1045, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')), u1_struct_0('#skF_5')) | k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r1_tarski('#skF_7', k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_658, c_1041])).
% 4.63/1.89  tff(c_1056, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')), u1_struct_0('#skF_5')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_76, c_48, c_46, c_40, c_38, c_487, c_36, c_1045])).
% 4.63/1.89  tff(c_1057, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')), u1_struct_0('#skF_5')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_301, c_248, c_285, c_1056])).
% 4.63/1.89  tff(c_1066, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_1057])).
% 4.63/1.89  tff(c_1079, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_1066])).
% 4.63/1.89  tff(c_1082, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_520, c_1079])).
% 4.63/1.89  tff(c_1089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1082])).
% 4.63/1.89  tff(c_1091, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1057])).
% 4.63/1.89  tff(c_304, plain, (![B_286, D_288, C_285, A_287, E_284]: (m1_subset_1('#skF_1'(E_284, C_285, B_286, A_287, D_288), A_287) | k2_partfun1(A_287, B_286, C_285, D_288)=E_284 | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(D_288, B_286))) | ~v1_funct_2(E_284, D_288, B_286) | ~v1_funct_1(E_284) | ~m1_subset_1(D_288, k1_zfmisc_1(A_287)) | v1_xboole_0(D_288) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_286))) | ~v1_funct_2(C_285, A_287, B_286) | ~v1_funct_1(C_285) | v1_xboole_0(B_286) | v1_xboole_0(A_287))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.89  tff(c_367, plain, (![A_300, A_301, D_297, B_299, C_298]: (m1_subset_1('#skF_1'(A_301, C_298, B_299, A_300, D_297), A_300) | k2_partfun1(A_300, B_299, C_298, D_297)=A_301 | ~v1_funct_2(A_301, D_297, B_299) | ~v1_funct_1(A_301) | ~m1_subset_1(D_297, k1_zfmisc_1(A_300)) | v1_xboole_0(D_297) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_300, B_299))) | ~v1_funct_2(C_298, A_300, B_299) | ~v1_funct_1(C_298) | v1_xboole_0(B_299) | v1_xboole_0(A_300) | ~r1_tarski(A_301, k2_zfmisc_1(D_297, B_299)))), inference(resolution, [status(thm)], [c_4, c_304])).
% 4.63/1.89  tff(c_394, plain, (![A_308, D_307, B_306, A_310, A_309]: (m1_subset_1('#skF_1'(A_310, A_309, B_306, A_308, D_307), A_308) | k2_partfun1(A_308, B_306, A_309, D_307)=A_310 | ~v1_funct_2(A_310, D_307, B_306) | ~v1_funct_1(A_310) | ~m1_subset_1(D_307, k1_zfmisc_1(A_308)) | v1_xboole_0(D_307) | ~v1_funct_2(A_309, A_308, B_306) | ~v1_funct_1(A_309) | v1_xboole_0(B_306) | v1_xboole_0(A_308) | ~r1_tarski(A_310, k2_zfmisc_1(D_307, B_306)) | ~r1_tarski(A_309, k2_zfmisc_1(A_308, B_306)))), inference(resolution, [status(thm)], [c_4, c_367])).
% 4.63/1.89  tff(c_404, plain, (![A_309, A_308]: (m1_subset_1('#skF_1'('#skF_7', A_309, u1_struct_0('#skF_3'), A_308, u1_struct_0('#skF_4')), A_308) | k2_partfun1(A_308, u1_struct_0('#skF_3'), A_309, u1_struct_0('#skF_4'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_308)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v1_funct_2(A_309, A_308, u1_struct_0('#skF_3')) | ~v1_funct_1(A_309) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_308) | ~r1_tarski(A_309, k2_zfmisc_1(A_308, u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_76, c_394])).
% 4.63/1.89  tff(c_413, plain, (![A_309, A_308]: (m1_subset_1('#skF_1'('#skF_7', A_309, u1_struct_0('#skF_3'), A_308, u1_struct_0('#skF_4')), A_308) | k2_partfun1(A_308, u1_struct_0('#skF_3'), A_309, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_308)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v1_funct_2(A_309, A_308, u1_struct_0('#skF_3')) | ~v1_funct_1(A_309) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_308) | ~r1_tarski(A_309, k2_zfmisc_1(A_308, u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_404])).
% 4.63/1.89  tff(c_414, plain, (![A_309, A_308]: (m1_subset_1('#skF_1'('#skF_7', A_309, u1_struct_0('#skF_3'), A_308, u1_struct_0('#skF_4')), A_308) | k2_partfun1(A_308, u1_struct_0('#skF_3'), A_309, u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_308)) | ~v1_funct_2(A_309, A_308, u1_struct_0('#skF_3')) | ~v1_funct_1(A_309) | v1_xboole_0(A_308) | ~r1_tarski(A_309, k2_zfmisc_1(A_308, u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_248, c_285, c_413])).
% 4.63/1.89  tff(c_1090, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')), u1_struct_0('#skF_5')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_1057])).
% 4.63/1.89  tff(c_1100, plain, (~m1_subset_1('#skF_1'('#skF_7', '#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1090])).
% 4.63/1.89  tff(c_1108, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | ~r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_414, c_1100])).
% 4.63/1.89  tff(c_1117, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7' | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_48, c_46, c_1091, c_487, c_1108])).
% 4.63/1.89  tff(c_1118, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_301, c_1117])).
% 4.63/1.89  tff(c_32, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_212])).
% 4.63/1.89  tff(c_1129, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1118, c_32])).
% 4.63/1.89  tff(c_1132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_1129])).
% 4.63/1.89  tff(c_1133, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_1090])).
% 4.63/1.89  tff(c_1137, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_32])).
% 4.63/1.89  tff(c_1140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_1137])).
% 4.63/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.89  
% 4.63/1.89  Inference rules
% 4.63/1.89  ----------------------
% 4.63/1.89  #Ref     : 1
% 4.63/1.89  #Sup     : 199
% 4.63/1.89  #Fact    : 0
% 4.63/1.89  #Define  : 0
% 4.63/1.89  #Split   : 11
% 4.63/1.89  #Chain   : 0
% 4.63/1.89  #Close   : 0
% 4.63/1.89  
% 4.63/1.89  Ordering : KBO
% 4.63/1.89  
% 4.63/1.89  Simplification rules
% 4.63/1.89  ----------------------
% 4.63/1.89  #Subsume      : 13
% 4.63/1.89  #Demod        : 280
% 4.63/1.89  #Tautology    : 60
% 4.63/1.89  #SimpNegUnit  : 56
% 4.63/1.89  #BackRed      : 7
% 4.63/1.89  
% 4.63/1.89  #Partial instantiations: 0
% 4.63/1.89  #Strategies tried      : 1
% 4.63/1.89  
% 4.63/1.89  Timing (in seconds)
% 4.63/1.89  ----------------------
% 4.63/1.89  Preprocessing        : 0.35
% 4.63/1.89  Parsing              : 0.18
% 4.63/1.89  CNF conversion       : 0.05
% 4.63/1.89  Main loop            : 0.65
% 4.63/1.89  Inferencing          : 0.22
% 4.63/1.89  Reduction            : 0.20
% 4.63/1.89  Demodulation         : 0.15
% 4.63/1.89  BG Simplification    : 0.03
% 4.63/1.89  Subsumption          : 0.16
% 4.63/1.89  Abstraction          : 0.03
% 4.63/1.89  MUC search           : 0.00
% 4.63/1.89  Cooper               : 0.00
% 4.63/1.89  Total                : 1.05
% 4.63/1.89  Index Insertion      : 0.00
% 4.63/1.89  Index Deletion       : 0.00
% 4.63/1.89  Index Matching       : 0.00
% 4.63/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
