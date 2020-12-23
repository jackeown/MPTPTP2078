%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:48 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 301 expanded)
%              Number of leaves         :   44 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  276 (2008 expanded)
%              Number of equality atoms :   26 (  81 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_259,negated_conjecture,(
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
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(B),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( v5_pre_topc(D,C,B)
                                & r1_tmap_1(B,A,E,F) )
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( r2_hidden(G,k8_relset_1(u1_struct_0(C),u1_struct_0(B),D,k6_domain_1(u1_struct_0(B),F)))
                                   => r1_tmap_1(C,A,k1_partfun1(u1_struct_0(C),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),D,E),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tmap_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( B != k1_xboole_0
       => ! [E] :
            ( r2_hidden(E,k8_relset_1(A,B,D,C))
          <=> ( r2_hidden(E,A)
              & r2_hidden(k1_funct_1(D,E),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_156,axiom,(
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

tff(f_207,axiom,(
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

tff(c_94,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_92,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_80,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_78,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_86,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_84,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_76,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_74,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_68,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_148,plain,(
    ! [A_313,B_314] :
      ( k6_domain_1(A_313,B_314) = k1_tarski(B_314)
      | ~ m1_subset_1(B_314,A_313)
      | v1_xboole_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_164,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_9') = k1_tarski('#skF_9')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_148])).

tff(c_186,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_42,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_189,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_186,c_42])).

tff(c_192,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_189])).

tff(c_195,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_195])).

tff(c_200,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_9') = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_56,plain,(
    r2_hidden('#skF_10',k8_relset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7',k6_domain_1(u1_struct_0('#skF_5'),'#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_203,plain,(
    r2_hidden('#skF_10',k8_relset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_56])).

tff(c_271,plain,(
    ! [D_335,B_334,A_336,C_332,E_333] :
      ( r2_hidden(E_333,A_336)
      | ~ r2_hidden(E_333,k8_relset_1(A_336,B_334,D_335,C_332))
      | k1_xboole_0 = B_334
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_334)))
      | ~ v1_funct_2(D_335,A_336,B_334)
      | ~ v1_funct_1(D_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_279,plain,
    ( r2_hidden('#skF_10',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_5') = k1_xboole_0
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_203,c_271])).

tff(c_284,plain,
    ( r2_hidden('#skF_10',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_279])).

tff(c_285,plain,(
    u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_201,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_290,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_201])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_290])).

tff(c_305,plain,(
    u1_struct_0('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_418,plain,(
    ! [C_353,B_355,A_357,D_356,E_354] :
      ( r2_hidden(k1_funct_1(D_356,E_354),C_353)
      | ~ r2_hidden(E_354,k8_relset_1(A_357,B_355,D_356,C_353))
      | k1_xboole_0 = B_355
      | ~ m1_subset_1(D_356,k1_zfmisc_1(k2_zfmisc_1(A_357,B_355)))
      | ~ v1_funct_2(D_356,A_357,B_355)
      | ~ v1_funct_1(D_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_426,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_10'),k1_tarski('#skF_9'))
    | u1_struct_0('#skF_5') = k1_xboole_0
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_203,c_418])).

tff(c_431,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_10'),k1_tarski('#skF_9'))
    | u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_426])).

tff(c_432,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_10'),k1_tarski('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_431])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_436,plain,(
    k1_funct_1('#skF_7','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_432,c_4])).

tff(c_163,plain,
    ( k6_domain_1(u1_struct_0('#skF_6'),'#skF_10') = k1_tarski('#skF_10')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_148])).

tff(c_165,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_169,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_165,c_42])).

tff(c_172,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_169])).

tff(c_175,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_175])).

tff(c_181,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_351,plain,(
    ! [A_347,B_348,C_349,D_350] :
      ( k3_funct_2(A_347,B_348,C_349,D_350) = k1_funct_1(C_349,D_350)
      | ~ m1_subset_1(D_350,A_347)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348)))
      | ~ v1_funct_2(C_349,A_347,B_348)
      | ~ v1_funct_1(C_349)
      | v1_xboole_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_363,plain,(
    ! [B_348,C_349] :
      ( k3_funct_2(u1_struct_0('#skF_6'),B_348,C_349,'#skF_10') = k1_funct_1(C_349,'#skF_10')
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),B_348)))
      | ~ v1_funct_2(C_349,u1_struct_0('#skF_6'),B_348)
      | ~ v1_funct_1(C_349)
      | v1_xboole_0(u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_58,c_351])).

tff(c_382,plain,(
    ! [B_351,C_352] :
      ( k3_funct_2(u1_struct_0('#skF_6'),B_351,C_352,'#skF_10') = k1_funct_1(C_352,'#skF_10')
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),B_351)))
      | ~ v1_funct_2(C_352,u1_struct_0('#skF_6'),B_351)
      | ~ v1_funct_1(C_352) ) ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_363])).

tff(c_385,plain,
    ( k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7','#skF_10') = k1_funct_1('#skF_7','#skF_10')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_382])).

tff(c_392,plain,(
    k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7','#skF_10') = k1_funct_1('#skF_7','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_385])).

tff(c_439,plain,(
    k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_392])).

tff(c_62,plain,(
    v5_pre_topc('#skF_7','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_794,plain,(
    ! [B_410,A_411,C_412,D_413] :
      ( r1_tmap_1(B_410,A_411,C_412,D_413)
      | ~ m1_subset_1(D_413,u1_struct_0(B_410))
      | ~ v5_pre_topc(C_412,B_410,A_411)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_410),u1_struct_0(A_411))))
      | ~ v1_funct_2(C_412,u1_struct_0(B_410),u1_struct_0(A_411))
      | ~ v1_funct_1(C_412)
      | ~ l1_pre_topc(B_410)
      | ~ v2_pre_topc(B_410)
      | v2_struct_0(B_410)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_804,plain,(
    ! [A_411,C_412] :
      ( r1_tmap_1('#skF_6',A_411,C_412,'#skF_10')
      | ~ v5_pre_topc(C_412,'#skF_6',A_411)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(A_411))))
      | ~ v1_funct_2(C_412,u1_struct_0('#skF_6'),u1_struct_0(A_411))
      | ~ v1_funct_1(C_412)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_58,c_794])).

tff(c_825,plain,(
    ! [A_411,C_412] :
      ( r1_tmap_1('#skF_6',A_411,C_412,'#skF_10')
      | ~ v5_pre_topc(C_412,'#skF_6',A_411)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(A_411))))
      | ~ v1_funct_2(C_412,u1_struct_0('#skF_6'),u1_struct_0(A_411))
      | ~ v1_funct_1(C_412)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_804])).

tff(c_831,plain,(
    ! [A_414,C_415] :
      ( r1_tmap_1('#skF_6',A_414,C_415,'#skF_10')
      | ~ v5_pre_topc(C_415,'#skF_6',A_414)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(A_414))))
      | ~ v1_funct_2(C_415,u1_struct_0('#skF_6'),u1_struct_0(A_414))
      | ~ v1_funct_1(C_415)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_825])).

tff(c_834,plain,
    ( r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_10')
    | ~ v5_pre_topc('#skF_7','#skF_6','#skF_5')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_831])).

tff(c_837,plain,
    ( r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_10')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_76,c_74,c_62,c_834])).

tff(c_838,plain,(
    r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_837])).

tff(c_60,plain,(
    r1_tmap_1('#skF_5','#skF_4','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_889,plain,(
    ! [C_436,A_437,D_434,F_435,B_433,E_438] :
      ( r1_tmap_1(B_433,A_437,k1_partfun1(u1_struct_0(B_433),u1_struct_0(C_436),u1_struct_0(C_436),u1_struct_0(A_437),D_434,E_438),F_435)
      | ~ r1_tmap_1(C_436,A_437,E_438,k3_funct_2(u1_struct_0(B_433),u1_struct_0(C_436),D_434,F_435))
      | ~ r1_tmap_1(B_433,C_436,D_434,F_435)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_433),u1_struct_0(C_436),D_434,F_435),u1_struct_0(C_436))
      | ~ m1_subset_1(F_435,u1_struct_0(B_433))
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_436),u1_struct_0(A_437))))
      | ~ v1_funct_2(E_438,u1_struct_0(C_436),u1_struct_0(A_437))
      | ~ v1_funct_1(E_438)
      | ~ m1_subset_1(D_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433),u1_struct_0(C_436))))
      | ~ v1_funct_2(D_434,u1_struct_0(B_433),u1_struct_0(C_436))
      | ~ v1_funct_1(D_434)
      | ~ l1_pre_topc(C_436)
      | ~ v2_pre_topc(C_436)
      | v2_struct_0(C_436)
      | ~ l1_pre_topc(B_433)
      | ~ v2_pre_topc(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_54,plain,(
    ~ r1_tmap_1('#skF_6','#skF_4',k1_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_7','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_895,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4','#skF_8',k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7','#skF_10'))
    | ~ r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_10')
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_7','#skF_10'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_889,c_54])).

tff(c_899,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_80,c_78,c_86,c_84,c_76,c_74,c_72,c_70,c_68,c_66,c_58,c_64,c_439,c_838,c_60,c_439,c_895])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_82,c_88,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.71  
% 3.94/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.71  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.94/1.71  
% 3.94/1.71  %Foreground sorts:
% 3.94/1.71  
% 3.94/1.71  
% 3.94/1.71  %Background operators:
% 3.94/1.71  
% 3.94/1.71  
% 3.94/1.71  %Foreground operators:
% 3.94/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.94/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.94/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.94/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.94/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.71  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.94/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.94/1.71  tff('#skF_7', type, '#skF_7': $i).
% 3.94/1.71  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.94/1.71  tff('#skF_10', type, '#skF_10': $i).
% 3.94/1.71  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.94/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.94/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.94/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.94/1.71  tff('#skF_9', type, '#skF_9': $i).
% 3.94/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.94/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.94/1.71  tff('#skF_8', type, '#skF_8': $i).
% 3.94/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.94/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.94/1.71  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.94/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.94/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.94/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.94/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.94/1.71  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.94/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.71  
% 3.94/1.73  tff(f_259, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => ((v5_pre_topc(D, C, B) & r1_tmap_1(B, A, E, F)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (r2_hidden(G, k8_relset_1(u1_struct_0(C), u1_struct_0(B), D, k6_domain_1(u1_struct_0(B), F))) => r1_tmap_1(C, A, k1_partfun1(u1_struct_0(C), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), D, E), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tmap_1)).
% 3.94/1.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.94/1.73  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.94/1.73  tff(f_127, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.94/1.73  tff(f_120, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.94/1.73  tff(f_108, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: (r2_hidden(E, k8_relset_1(A, B, D, C)) <=> (r2_hidden(E, A) & r2_hidden(k1_funct_1(D, E), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_2)).
% 3.94/1.73  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.94/1.73  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.94/1.73  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 3.94/1.73  tff(f_207, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 3.94/1.73  tff(c_94, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_82, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_88, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_92, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_80, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_78, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_86, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_84, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_76, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_74, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_68, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_58, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_64, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.94/1.73  tff(c_40, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.94/1.73  tff(c_148, plain, (![A_313, B_314]: (k6_domain_1(A_313, B_314)=k1_tarski(B_314) | ~m1_subset_1(B_314, A_313) | v1_xboole_0(A_313))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.94/1.73  tff(c_164, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_9')=k1_tarski('#skF_9') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_148])).
% 3.94/1.73  tff(c_186, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_164])).
% 3.94/1.73  tff(c_42, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.94/1.73  tff(c_189, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_186, c_42])).
% 3.94/1.73  tff(c_192, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_88, c_189])).
% 3.94/1.73  tff(c_195, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_192])).
% 3.94/1.73  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_195])).
% 3.94/1.73  tff(c_200, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_9')=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_164])).
% 3.94/1.73  tff(c_56, plain, (r2_hidden('#skF_10', k8_relset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', k6_domain_1(u1_struct_0('#skF_5'), '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_203, plain, (r2_hidden('#skF_10', k8_relset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_56])).
% 3.94/1.73  tff(c_271, plain, (![D_335, B_334, A_336, C_332, E_333]: (r2_hidden(E_333, A_336) | ~r2_hidden(E_333, k8_relset_1(A_336, B_334, D_335, C_332)) | k1_xboole_0=B_334 | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_334))) | ~v1_funct_2(D_335, A_336, B_334) | ~v1_funct_1(D_335))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.94/1.73  tff(c_279, plain, (r2_hidden('#skF_10', u1_struct_0('#skF_6')) | u1_struct_0('#skF_5')=k1_xboole_0 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_203, c_271])).
% 3.94/1.73  tff(c_284, plain, (r2_hidden('#skF_10', u1_struct_0('#skF_6')) | u1_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_279])).
% 3.94/1.73  tff(c_285, plain, (u1_struct_0('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_284])).
% 3.94/1.73  tff(c_201, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_164])).
% 3.94/1.73  tff(c_290, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_285, c_201])).
% 3.94/1.73  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_290])).
% 3.94/1.73  tff(c_305, plain, (u1_struct_0('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_284])).
% 3.94/1.73  tff(c_418, plain, (![C_353, B_355, A_357, D_356, E_354]: (r2_hidden(k1_funct_1(D_356, E_354), C_353) | ~r2_hidden(E_354, k8_relset_1(A_357, B_355, D_356, C_353)) | k1_xboole_0=B_355 | ~m1_subset_1(D_356, k1_zfmisc_1(k2_zfmisc_1(A_357, B_355))) | ~v1_funct_2(D_356, A_357, B_355) | ~v1_funct_1(D_356))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.94/1.73  tff(c_426, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_10'), k1_tarski('#skF_9')) | u1_struct_0('#skF_5')=k1_xboole_0 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_203, c_418])).
% 3.94/1.73  tff(c_431, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_10'), k1_tarski('#skF_9')) | u1_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_426])).
% 3.94/1.73  tff(c_432, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_10'), k1_tarski('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_305, c_431])).
% 3.94/1.73  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.94/1.73  tff(c_436, plain, (k1_funct_1('#skF_7', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_432, c_4])).
% 3.94/1.73  tff(c_163, plain, (k6_domain_1(u1_struct_0('#skF_6'), '#skF_10')=k1_tarski('#skF_10') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_148])).
% 3.94/1.73  tff(c_165, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_163])).
% 3.94/1.73  tff(c_169, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_165, c_42])).
% 3.94/1.73  tff(c_172, plain, (~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_82, c_169])).
% 3.94/1.73  tff(c_175, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_172])).
% 3.94/1.73  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_175])).
% 3.94/1.73  tff(c_181, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_163])).
% 3.94/1.73  tff(c_351, plain, (![A_347, B_348, C_349, D_350]: (k3_funct_2(A_347, B_348, C_349, D_350)=k1_funct_1(C_349, D_350) | ~m1_subset_1(D_350, A_347) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))) | ~v1_funct_2(C_349, A_347, B_348) | ~v1_funct_1(C_349) | v1_xboole_0(A_347))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.94/1.73  tff(c_363, plain, (![B_348, C_349]: (k3_funct_2(u1_struct_0('#skF_6'), B_348, C_349, '#skF_10')=k1_funct_1(C_349, '#skF_10') | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), B_348))) | ~v1_funct_2(C_349, u1_struct_0('#skF_6'), B_348) | ~v1_funct_1(C_349) | v1_xboole_0(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_58, c_351])).
% 3.94/1.73  tff(c_382, plain, (![B_351, C_352]: (k3_funct_2(u1_struct_0('#skF_6'), B_351, C_352, '#skF_10')=k1_funct_1(C_352, '#skF_10') | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), B_351))) | ~v1_funct_2(C_352, u1_struct_0('#skF_6'), B_351) | ~v1_funct_1(C_352))), inference(negUnitSimplification, [status(thm)], [c_181, c_363])).
% 3.94/1.73  tff(c_385, plain, (k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', '#skF_10')=k1_funct_1('#skF_7', '#skF_10') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_382])).
% 3.94/1.73  tff(c_392, plain, (k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', '#skF_10')=k1_funct_1('#skF_7', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_385])).
% 3.94/1.73  tff(c_439, plain, (k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_436, c_392])).
% 3.94/1.73  tff(c_62, plain, (v5_pre_topc('#skF_7', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_794, plain, (![B_410, A_411, C_412, D_413]: (r1_tmap_1(B_410, A_411, C_412, D_413) | ~m1_subset_1(D_413, u1_struct_0(B_410)) | ~v5_pre_topc(C_412, B_410, A_411) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_410), u1_struct_0(A_411)))) | ~v1_funct_2(C_412, u1_struct_0(B_410), u1_struct_0(A_411)) | ~v1_funct_1(C_412) | ~l1_pre_topc(B_410) | ~v2_pre_topc(B_410) | v2_struct_0(B_410) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.94/1.73  tff(c_804, plain, (![A_411, C_412]: (r1_tmap_1('#skF_6', A_411, C_412, '#skF_10') | ~v5_pre_topc(C_412, '#skF_6', A_411) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(A_411)))) | ~v1_funct_2(C_412, u1_struct_0('#skF_6'), u1_struct_0(A_411)) | ~v1_funct_1(C_412) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(resolution, [status(thm)], [c_58, c_794])).
% 3.94/1.73  tff(c_825, plain, (![A_411, C_412]: (r1_tmap_1('#skF_6', A_411, C_412, '#skF_10') | ~v5_pre_topc(C_412, '#skF_6', A_411) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(A_411)))) | ~v1_funct_2(C_412, u1_struct_0('#skF_6'), u1_struct_0(A_411)) | ~v1_funct_1(C_412) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_804])).
% 3.94/1.73  tff(c_831, plain, (![A_414, C_415]: (r1_tmap_1('#skF_6', A_414, C_415, '#skF_10') | ~v5_pre_topc(C_415, '#skF_6', A_414) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(A_414)))) | ~v1_funct_2(C_415, u1_struct_0('#skF_6'), u1_struct_0(A_414)) | ~v1_funct_1(C_415) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414))), inference(negUnitSimplification, [status(thm)], [c_82, c_825])).
% 3.94/1.73  tff(c_834, plain, (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_10') | ~v5_pre_topc('#skF_7', '#skF_6', '#skF_5') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_831])).
% 3.94/1.73  tff(c_837, plain, (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_10') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_76, c_74, c_62, c_834])).
% 3.94/1.73  tff(c_838, plain, (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_88, c_837])).
% 3.94/1.73  tff(c_60, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_889, plain, (![C_436, A_437, D_434, F_435, B_433, E_438]: (r1_tmap_1(B_433, A_437, k1_partfun1(u1_struct_0(B_433), u1_struct_0(C_436), u1_struct_0(C_436), u1_struct_0(A_437), D_434, E_438), F_435) | ~r1_tmap_1(C_436, A_437, E_438, k3_funct_2(u1_struct_0(B_433), u1_struct_0(C_436), D_434, F_435)) | ~r1_tmap_1(B_433, C_436, D_434, F_435) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_433), u1_struct_0(C_436), D_434, F_435), u1_struct_0(C_436)) | ~m1_subset_1(F_435, u1_struct_0(B_433)) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_436), u1_struct_0(A_437)))) | ~v1_funct_2(E_438, u1_struct_0(C_436), u1_struct_0(A_437)) | ~v1_funct_1(E_438) | ~m1_subset_1(D_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433), u1_struct_0(C_436)))) | ~v1_funct_2(D_434, u1_struct_0(B_433), u1_struct_0(C_436)) | ~v1_funct_1(D_434) | ~l1_pre_topc(C_436) | ~v2_pre_topc(C_436) | v2_struct_0(C_436) | ~l1_pre_topc(B_433) | ~v2_pre_topc(B_433) | v2_struct_0(B_433) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.94/1.73  tff(c_54, plain, (~r1_tmap_1('#skF_6', '#skF_4', k1_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), '#skF_7', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_259])).
% 3.94/1.73  tff(c_895, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_8', k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', '#skF_10')) | ~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_10') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_7', '#skF_10'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_889, c_54])).
% 3.94/1.73  tff(c_899, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_80, c_78, c_86, c_84, c_76, c_74, c_72, c_70, c_68, c_66, c_58, c_64, c_439, c_838, c_60, c_439, c_895])).
% 3.94/1.73  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_82, c_88, c_899])).
% 3.94/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.73  
% 3.94/1.73  Inference rules
% 3.94/1.73  ----------------------
% 3.94/1.73  #Ref     : 0
% 3.94/1.73  #Sup     : 158
% 3.94/1.73  #Fact    : 0
% 3.94/1.73  #Define  : 0
% 3.94/1.73  #Split   : 11
% 3.94/1.73  #Chain   : 0
% 3.94/1.73  #Close   : 0
% 3.94/1.73  
% 3.94/1.73  Ordering : KBO
% 3.94/1.73  
% 3.94/1.73  Simplification rules
% 3.94/1.73  ----------------------
% 3.94/1.73  #Subsume      : 3
% 3.94/1.73  #Demod        : 215
% 3.94/1.73  #Tautology    : 77
% 3.94/1.73  #SimpNegUnit  : 35
% 3.94/1.73  #BackRed      : 17
% 3.94/1.73  
% 3.94/1.73  #Partial instantiations: 0
% 3.94/1.73  #Strategies tried      : 1
% 3.94/1.73  
% 3.94/1.73  Timing (in seconds)
% 3.94/1.73  ----------------------
% 3.94/1.73  Preprocessing        : 0.44
% 3.94/1.73  Parsing              : 0.23
% 3.94/1.73  CNF conversion       : 0.05
% 3.94/1.73  Main loop            : 0.46
% 3.94/1.73  Inferencing          : 0.16
% 3.94/1.73  Reduction            : 0.15
% 3.94/1.73  Demodulation         : 0.10
% 3.94/1.73  BG Simplification    : 0.03
% 3.94/1.73  Subsumption          : 0.08
% 3.94/1.73  Abstraction          : 0.03
% 3.94/1.73  MUC search           : 0.00
% 3.94/1.73  Cooper               : 0.00
% 3.94/1.73  Total                : 0.93
% 3.94/1.73  Index Insertion      : 0.00
% 3.94/1.73  Index Deletion       : 0.00
% 3.94/1.73  Index Matching       : 0.00
% 3.94/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
