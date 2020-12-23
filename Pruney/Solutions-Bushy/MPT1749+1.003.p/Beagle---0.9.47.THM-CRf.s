%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1749+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:20 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 859 expanded)
%              Number of leaves         :   37 ( 320 expanded)
%              Depth                    :   21
%              Number of atoms          :  419 (7273 expanded)
%              Number of equality atoms :   44 ( 553 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_216,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                       => ( ! [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                             => ( r2_hidden(F,u1_struct_0(C))
                               => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_46,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_44,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_136,plain,(
    ! [A_190,B_191,D_192] :
      ( r2_funct_2(A_190,B_191,D_192,D_192)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_2(D_192,A_190,B_191)
      | ~ v1_funct_1(D_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_140,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_149,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_140])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_14,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_205,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( v1_funct_1(k2_tmap_1(A_219,B_220,C_221,D_222))
      | ~ l1_struct_0(D_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_219),u1_struct_0(B_220))))
      | ~ v1_funct_2(C_221,u1_struct_0(A_219),u1_struct_0(B_220))
      | ~ v1_funct_1(C_221)
      | ~ l1_struct_0(B_220)
      | ~ l1_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_210,plain,(
    ! [D_222] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_6',D_222))
      | ~ l1_struct_0(D_222)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_205])).

tff(c_219,plain,(
    ! [D_222] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_6',D_222))
      | ~ l1_struct_0(D_222)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_210])).

tff(c_224,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_227,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_227])).

tff(c_233,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_232,plain,(
    ! [D_222] :
      ( ~ l1_struct_0('#skF_3')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_6',D_222))
      | ~ l1_struct_0(D_222) ) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_244,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_247,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_244])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_247])).

tff(c_253,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_504,plain,(
    ! [A_285,B_289,E_288,D_286,C_287] :
      ( m1_subset_1('#skF_2'(A_285,D_286,C_287,E_288,B_289),A_285)
      | k2_partfun1(A_285,B_289,C_287,D_286) = E_288
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(D_286,B_289)))
      | ~ v1_funct_2(E_288,D_286,B_289)
      | ~ v1_funct_1(E_288)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(A_285))
      | v1_xboole_0(D_286)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_289)))
      | ~ v1_funct_2(C_287,A_285,B_289)
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(B_289)
      | v1_xboole_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_514,plain,(
    ! [A_285,C_287] :
      ( m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_5'),C_287,'#skF_7',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_42,c_504])).

tff(c_526,plain,(
    ! [A_285,C_287] :
      ( m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_5'),C_287,'#skF_7',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_514])).

tff(c_644,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_20,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_649,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_20])).

tff(c_655,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_649])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_655])).

tff(c_659,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_512,plain,(
    ! [A_285,C_287] :
      ( m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_4'),C_287,'#skF_6',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_48,c_504])).

tff(c_523,plain,(
    ! [A_285,C_287] :
      ( m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_4'),C_287,'#skF_6',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_512])).

tff(c_676,plain,(
    ! [A_285,C_287] :
      ( m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_4'),C_287,'#skF_6',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_285))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(A_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_659,c_523])).

tff(c_677,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_676])).

tff(c_682,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_677,c_20])).

tff(c_688,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_682])).

tff(c_690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_688])).

tff(c_692,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_32,plain,(
    ! [B_99,A_97] :
      ( m1_subset_1(u1_struct_0(B_99),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_pre_topc(B_99,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_72,plain,(
    ! [B_166,A_167] :
      ( l1_pre_topc(B_166)
      | ~ m1_pre_topc(B_166,A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_75,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_75])).

tff(c_212,plain,(
    ! [D_222] :
      ( v1_funct_1(k2_tmap_1('#skF_5','#skF_3','#skF_7',D_222))
      | ~ l1_struct_0(D_222)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_205])).

tff(c_222,plain,(
    ! [D_222] :
      ( v1_funct_1(k2_tmap_1('#skF_5','#skF_3','#skF_7',D_222))
      | ~ l1_struct_0(D_222)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_212])).

tff(c_234,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_237,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_237])).

tff(c_243,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_658,plain,(
    ! [A_285,C_287] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_5'),C_287,'#skF_7',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(A_285) ) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_660,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_658])).

tff(c_665,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_660,c_20])).

tff(c_671,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_665])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_671])).

tff(c_675,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_658])).

tff(c_426,plain,(
    ! [C_275,D_274,A_273,E_276,B_277] :
      ( r2_hidden('#skF_2'(A_273,D_274,C_275,E_276,B_277),D_274)
      | k2_partfun1(A_273,B_277,C_275,D_274) = E_276
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(D_274,B_277)))
      | ~ v1_funct_2(E_276,D_274,B_277)
      | ~ v1_funct_1(E_276)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(A_273))
      | v1_xboole_0(D_274)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_277)))
      | ~ v1_funct_2(C_275,A_273,B_277)
      | ~ v1_funct_1(C_275)
      | v1_xboole_0(B_277)
      | v1_xboole_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_436,plain,(
    ! [A_273,C_275] :
      ( r2_hidden('#skF_2'(A_273,u1_struct_0('#skF_5'),C_275,'#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_275,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_273))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_275,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_275)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_42,c_426])).

tff(c_448,plain,(
    ! [A_273,C_275] :
      ( r2_hidden('#skF_2'(A_273,u1_struct_0('#skF_5'),C_275,'#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_275,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_273))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_275,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_275)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_436])).

tff(c_793,plain,(
    ! [A_273,C_275] :
      ( r2_hidden('#skF_2'(A_273,u1_struct_0('#skF_5'),C_275,'#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_273,u1_struct_0('#skF_3'),C_275,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_273))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_275,A_273,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_275)
      | v1_xboole_0(A_273) ) ),
    inference(negUnitSimplification,[status(thm)],[c_659,c_675,c_448])).

tff(c_40,plain,(
    ! [F_162] :
      ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',F_162) = k1_funct_1('#skF_7',F_162)
      | ~ r2_hidden(F_162,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_162,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_591,plain,(
    ! [D_317,E_319,C_318,B_320,A_316] :
      ( k3_funct_2(A_316,B_320,C_318,'#skF_2'(A_316,D_317,C_318,E_319,B_320)) != k1_funct_1(E_319,'#skF_2'(A_316,D_317,C_318,E_319,B_320))
      | k2_partfun1(A_316,B_320,C_318,D_317) = E_319
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(D_317,B_320)))
      | ~ v1_funct_2(E_319,D_317,B_320)
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(A_316))
      | v1_xboole_0(D_317)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_320)))
      | ~ v1_funct_2(C_318,A_316,B_320)
      | ~ v1_funct_1(C_318)
      | v1_xboole_0(B_320)
      | v1_xboole_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_594,plain,(
    ! [E_319,D_317] :
      ( k1_funct_1(E_319,'#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3'))) != k1_funct_1('#skF_7','#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_317) = E_319
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(D_317,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_319,D_317,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_317)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_591])).

tff(c_596,plain,(
    ! [E_319,D_317] :
      ( k1_funct_1(E_319,'#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3'))) != k1_funct_1('#skF_7','#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_317) = E_319
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(D_317,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_319,D_317,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_317)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_594])).

tff(c_1036,plain,(
    ! [E_319,D_317] :
      ( k1_funct_1(E_319,'#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3'))) != k1_funct_1('#skF_7','#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_317) = E_319
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(D_317,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_319,D_317,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_319)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_317)
      | ~ r2_hidden('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6',E_319,u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_659,c_596])).

tff(c_1039,plain,(
    ! [D_317] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_317) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_317,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_317,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_317)
      | ~ r2_hidden('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),D_317,'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1036])).

tff(c_1043,plain,(
    ! [D_424] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_424) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_424,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_424,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_424,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_424)
      | ~ r2_hidden('#skF_2'(u1_struct_0('#skF_4'),D_424,'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),D_424,'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1039])).

tff(c_1047,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_793,c_1043])).

tff(c_1053,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_44,c_42,c_1047])).

tff(c_1054,plain,
    ( ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_675,c_1053])).

tff(c_1058,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1061,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1058])).

tff(c_1065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1061])).

tff(c_1067,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_674,plain,(
    ! [A_285,C_287] :
      ( m1_subset_1('#skF_2'(A_285,u1_struct_0('#skF_5'),C_287,'#skF_7',u1_struct_0('#skF_3')),A_285)
      | k2_partfun1(A_285,u1_struct_0('#skF_3'),C_287,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_285))
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_287,A_285,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_287)
      | v1_xboole_0(A_285) ) ),
    inference(splitRight,[status(thm)],[c_658])).

tff(c_1066,plain,
    ( ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_1071,plain,(
    ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7',u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1066])).

tff(c_1094,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_674,c_1071])).

tff(c_1097,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1067,c_1094])).

tff(c_1098,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_1097])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_335,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k2_partfun1(u1_struct_0(A_264),u1_struct_0(B_265),C_266,u1_struct_0(D_267)) = k2_tmap_1(A_264,B_265,C_266,D_267)
      | ~ m1_pre_topc(D_267,A_264)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_264),u1_struct_0(B_265))))
      | ~ v1_funct_2(C_266,u1_struct_0(A_264),u1_struct_0(B_265))
      | ~ v1_funct_1(C_266)
      | ~ l1_pre_topc(B_265)
      | ~ v2_pre_topc(B_265)
      | v2_struct_0(B_265)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_342,plain,(
    ! [D_267] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_267)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_267)
      | ~ m1_pre_topc(D_267,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_335])).

tff(c_352,plain,(
    ! [D_267] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_267)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_267)
      | ~ m1_pre_topc(D_267,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_66,c_64,c_52,c_50,c_342])).

tff(c_353,plain,(
    ! [D_267] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_267)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_267)
      | ~ m1_pre_topc(D_267,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_352])).

tff(c_1126,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7'
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_353])).

tff(c_1166,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1126])).

tff(c_38,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1179,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1166,c_38])).

tff(c_1182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1179])).

tff(c_1183,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1066])).

tff(c_1256,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7'
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_353])).

tff(c_1296,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1256])).

tff(c_1309,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_38])).

tff(c_1312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1309])).

%------------------------------------------------------------------------------
