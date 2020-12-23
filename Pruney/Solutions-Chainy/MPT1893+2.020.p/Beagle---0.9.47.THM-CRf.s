%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:28 EST 2020

% Result     : Theorem 8.38s
% Output     : CNFRefutation 8.38s
% Verified   : 
% Statistics : Number of formulae       :  172 (2102 expanded)
%              Number of leaves         :   46 ( 724 expanded)
%              Depth                    :   23
%              Number of atoms          :  460 (8172 expanded)
%              Number of equality atoms :   59 ( 962 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( B = k1_tarski(C)
                 => v3_pre_topc(B,A) ) ) )
       => v1_tdlat_3(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_157,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_82,plain,(
    v3_tex_2('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_88,plain,(
    l1_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_86,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_209,plain,(
    ! [A_101,B_102] :
      ( k2_pre_topc(A_101,B_102) = B_102
      | ~ v4_pre_topc(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_225,plain,
    ( k2_pre_topc('#skF_9','#skF_10') = '#skF_10'
    | ~ v4_pre_topc('#skF_10','#skF_9')
    | ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_209])).

tff(c_236,plain,
    ( k2_pre_topc('#skF_9','#skF_10') = '#skF_10'
    | ~ v4_pre_topc('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_225])).

tff(c_238,plain,(
    ~ v4_pre_topc('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_92,plain,(
    v2_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_90,plain,(
    v3_tdlat_3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_84,plain,
    ( v4_pre_topc('#skF_10','#skF_9')
    | v3_pre_topc('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_106,plain,(
    v3_pre_topc('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_611,plain,(
    ! [B_138,A_139] :
      ( v4_pre_topc(B_138,A_139)
      | ~ v3_pre_topc(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ v3_tdlat_3(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_627,plain,
    ( v4_pre_topc('#skF_10','#skF_9')
    | ~ v3_pre_topc('#skF_10','#skF_9')
    | ~ v3_tdlat_3('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_611])).

tff(c_638,plain,(
    v4_pre_topc('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_90,c_106,c_627])).

tff(c_640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_638])).

tff(c_641,plain,(
    k2_pre_topc('#skF_9','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_648,plain,(
    ! [B_141,A_142] :
      ( v1_tops_1(B_141,A_142)
      | k2_pre_topc(A_142,B_141) != u1_struct_0(A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_664,plain,
    ( v1_tops_1('#skF_10','#skF_9')
    | k2_pre_topc('#skF_9','#skF_10') != u1_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_648])).

tff(c_675,plain,
    ( v1_tops_1('#skF_10','#skF_9')
    | u1_struct_0('#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_641,c_664])).

tff(c_677,plain,(
    u1_struct_0('#skF_9') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_675])).

tff(c_727,plain,(
    ! [A_148,B_149] :
      ( k2_pre_topc(A_148,B_149) = u1_struct_0(A_148)
      | ~ v1_tops_1(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_743,plain,
    ( k2_pre_topc('#skF_9','#skF_10') = u1_struct_0('#skF_9')
    | ~ v1_tops_1('#skF_10','#skF_9')
    | ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_727])).

tff(c_754,plain,
    ( u1_struct_0('#skF_9') = '#skF_10'
    | ~ v1_tops_1('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_641,c_743])).

tff(c_755,plain,(
    ~ v1_tops_1('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_677,c_754])).

tff(c_1522,plain,(
    ! [B_217,A_218] :
      ( v1_tops_1(B_217,A_218)
      | ~ v3_tex_2(B_217,A_218)
      | ~ v3_pre_topc(B_217,A_218)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1544,plain,
    ( v1_tops_1('#skF_10','#skF_9')
    | ~ v3_tex_2('#skF_10','#skF_9')
    | ~ v3_pre_topc('#skF_10','#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_1522])).

tff(c_1557,plain,
    ( v1_tops_1('#skF_10','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_106,c_82,c_1544])).

tff(c_1559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_755,c_1557])).

tff(c_1561,plain,(
    u1_struct_0('#skF_9') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_80,plain,(
    v1_subset_1('#skF_10',u1_struct_0('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1564,plain,(
    v1_subset_1('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_80])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_143,plain,(
    ! [A_92] :
      ( m1_subset_1('#skF_4'(A_92),k1_zfmisc_1(u1_struct_0(A_92)))
      | v1_tdlat_3(A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_4'(A_92),u1_struct_0(A_92))
      | v1_tdlat_3(A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_143,c_6])).

tff(c_1591,plain,
    ( r1_tarski('#skF_4'('#skF_9'),'#skF_10')
    | v1_tdlat_3('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_147])).

tff(c_1624,plain,
    ( r1_tarski('#skF_4'('#skF_9'),'#skF_10')
    | v1_tdlat_3('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_1591])).

tff(c_1636,plain,(
    v1_tdlat_3('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1624])).

tff(c_3758,plain,(
    ! [B_359,A_360] :
      ( ~ v1_subset_1(B_359,u1_struct_0(A_360))
      | ~ v3_tex_2(B_359,A_360)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ l1_pre_topc(A_360)
      | ~ v1_tdlat_3(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_3767,plain,(
    ! [B_359] :
      ( ~ v1_subset_1(B_359,u1_struct_0('#skF_9'))
      | ~ v3_tex_2(B_359,'#skF_9')
      | ~ m1_subset_1(B_359,k1_zfmisc_1('#skF_10'))
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_tdlat_3('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_3758])).

tff(c_3788,plain,(
    ! [B_359] :
      ( ~ v1_subset_1(B_359,'#skF_10')
      | ~ v3_tex_2(B_359,'#skF_9')
      | ~ m1_subset_1(B_359,k1_zfmisc_1('#skF_10'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1636,c_88,c_1561,c_3767])).

tff(c_3795,plain,(
    ! [B_361] :
      ( ~ v1_subset_1(B_361,'#skF_10')
      | ~ v3_tex_2(B_361,'#skF_9')
      | ~ m1_subset_1(B_361,k1_zfmisc_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3788])).

tff(c_3809,plain,
    ( ~ v1_subset_1('#skF_10','#skF_10')
    | ~ v3_tex_2('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_95,c_3795])).

tff(c_3816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1564,c_3809])).

tff(c_3818,plain,(
    ~ v1_tdlat_3('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1624])).

tff(c_48,plain,(
    ! [A_46] :
      ( m1_subset_1('#skF_4'(A_46),k1_zfmisc_1(u1_struct_0(A_46)))
      | v1_tdlat_3(A_46)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1597,plain,
    ( m1_subset_1('#skF_4'('#skF_9'),k1_zfmisc_1('#skF_10'))
    | v1_tdlat_3('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_48])).

tff(c_1628,plain,
    ( m1_subset_1('#skF_4'('#skF_9'),k1_zfmisc_1('#skF_10'))
    | v1_tdlat_3('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_1597])).

tff(c_3820,plain,(
    m1_subset_1('#skF_4'('#skF_9'),k1_zfmisc_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_3818,c_1628])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( k2_pre_topc(A_5,B_7) = B_7
      | ~ v4_pre_topc(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1576,plain,(
    ! [B_7] :
      ( k2_pre_topc('#skF_9',B_7) = B_7
      | ~ v4_pre_topc(B_7,'#skF_9')
      | ~ m1_subset_1(B_7,k1_zfmisc_1('#skF_10'))
      | ~ l1_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_12])).

tff(c_3879,plain,(
    ! [B_366] :
      ( k2_pre_topc('#skF_9',B_366) = B_366
      | ~ v4_pre_topc(B_366,'#skF_9')
      | ~ m1_subset_1(B_366,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1576])).

tff(c_3891,plain,
    ( k2_pre_topc('#skF_9','#skF_4'('#skF_9')) = '#skF_4'('#skF_9')
    | ~ v4_pre_topc('#skF_4'('#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_3820,c_3879])).

tff(c_3896,plain,(
    ~ v4_pre_topc('#skF_4'('#skF_9'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3891])).

tff(c_4104,plain,(
    ! [B_383,A_384] :
      ( v4_pre_topc(B_383,A_384)
      | k2_pre_topc(A_384,B_383) != B_383
      | ~ v2_pre_topc(A_384)
      | ~ m1_subset_1(B_383,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ l1_pre_topc(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4107,plain,(
    ! [B_383] :
      ( v4_pre_topc(B_383,'#skF_9')
      | k2_pre_topc('#skF_9',B_383) != B_383
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1(B_383,k1_zfmisc_1('#skF_10'))
      | ~ l1_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_4104])).

tff(c_4132,plain,(
    ! [B_385] :
      ( v4_pre_topc(B_385,'#skF_9')
      | k2_pre_topc('#skF_9',B_385) != B_385
      | ~ m1_subset_1(B_385,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_92,c_4107])).

tff(c_4135,plain,
    ( v4_pre_topc('#skF_4'('#skF_9'),'#skF_9')
    | k2_pre_topc('#skF_9','#skF_4'('#skF_9')) != '#skF_4'('#skF_9') ),
    inference(resolution,[status(thm)],[c_3820,c_4132])).

tff(c_4146,plain,(
    k2_pre_topc('#skF_9','#skF_4'('#skF_9')) != '#skF_4'('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_3896,c_4135])).

tff(c_3817,plain,(
    r1_tarski('#skF_4'('#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_1624])).

tff(c_155,plain,(
    ! [B_96,A_97] :
      ( v2_tex_2(B_96,A_97)
      | ~ v3_tex_2(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_171,plain,
    ( v2_tex_2('#skF_10','#skF_9')
    | ~ v3_tex_2('#skF_10','#skF_9')
    | ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_155])).

tff(c_182,plain,(
    v2_tex_2('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_171])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6967,plain,(
    ! [A_581,B_582,C_583] :
      ( k9_subset_1(u1_struct_0(A_581),B_582,'#skF_1'(A_581,B_582,C_583)) = C_583
      | ~ r1_tarski(C_583,B_582)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ v2_tex_2(B_582,A_581)
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ l1_pre_topc(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6977,plain,(
    ! [B_582,C_583] :
      ( k9_subset_1(u1_struct_0('#skF_9'),B_582,'#skF_1'('#skF_9',B_582,C_583)) = C_583
      | ~ r1_tarski(C_583,B_582)
      | ~ m1_subset_1(C_583,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_582,'#skF_9')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ l1_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_6967])).

tff(c_7149,plain,(
    ! [B_588,C_589] :
      ( k9_subset_1('#skF_10',B_588,'#skF_1'('#skF_9',B_588,C_589)) = C_589
      | ~ r1_tarski(C_589,B_588)
      | ~ m1_subset_1(C_589,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_588,'#skF_9')
      | ~ m1_subset_1(B_588,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1561,c_1561,c_6977])).

tff(c_7922,plain,(
    ! [B_625,A_626] :
      ( k9_subset_1('#skF_10',B_625,'#skF_1'('#skF_9',B_625,A_626)) = A_626
      | ~ r1_tarski(A_626,B_625)
      | ~ v2_tex_2(B_625,'#skF_9')
      | ~ m1_subset_1(B_625,k1_zfmisc_1('#skF_10'))
      | ~ r1_tarski(A_626,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_8,c_7149])).

tff(c_7938,plain,(
    ! [A_626] :
      ( k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10',A_626)) = A_626
      | ~ v2_tex_2('#skF_10','#skF_9')
      | ~ r1_tarski(A_626,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_95,c_7922])).

tff(c_7986,plain,(
    ! [A_628] :
      ( k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10',A_628)) = A_628
      | ~ r1_tarski(A_628,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_7938])).

tff(c_6735,plain,(
    ! [A_564,B_565,C_566] :
      ( m1_subset_1('#skF_1'(A_564,B_565,C_566),k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ r1_tarski(C_566,B_565)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ v2_tex_2(B_565,A_564)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ l1_pre_topc(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6784,plain,(
    ! [B_565,C_566] :
      ( m1_subset_1('#skF_1'('#skF_9',B_565,C_566),k1_zfmisc_1('#skF_10'))
      | ~ r1_tarski(C_566,B_565)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ v2_tex_2(B_565,'#skF_9')
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ l1_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_6735])).

tff(c_6804,plain,(
    ! [B_567,C_568] :
      ( m1_subset_1('#skF_1'('#skF_9',B_567,C_568),k1_zfmisc_1('#skF_10'))
      | ~ r1_tarski(C_568,B_567)
      | ~ m1_subset_1(C_568,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_567,'#skF_9')
      | ~ m1_subset_1(B_567,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1561,c_1561,c_6784])).

tff(c_6844,plain,(
    ! [B_567,C_568] :
      ( r1_tarski('#skF_1'('#skF_9',B_567,C_568),'#skF_10')
      | ~ r1_tarski(C_568,B_567)
      | ~ m1_subset_1(C_568,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_567,'#skF_9')
      | ~ m1_subset_1(B_567,k1_zfmisc_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_6804,c_6])).

tff(c_6482,plain,(
    ! [A_533,B_534,C_535] :
      ( v3_pre_topc('#skF_1'(A_533,B_534,C_535),A_533)
      | ~ r1_tarski(C_535,B_534)
      | ~ m1_subset_1(C_535,k1_zfmisc_1(u1_struct_0(A_533)))
      | ~ v2_tex_2(B_534,A_533)
      | ~ m1_subset_1(B_534,k1_zfmisc_1(u1_struct_0(A_533)))
      | ~ l1_pre_topc(A_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7513,plain,(
    ! [A_605,B_606,A_607] :
      ( v3_pre_topc('#skF_1'(A_605,B_606,A_607),A_605)
      | ~ r1_tarski(A_607,B_606)
      | ~ v2_tex_2(B_606,A_605)
      | ~ m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0(A_605)))
      | ~ l1_pre_topc(A_605)
      | ~ r1_tarski(A_607,u1_struct_0(A_605)) ) ),
    inference(resolution,[status(thm)],[c_8,c_6482])).

tff(c_7547,plain,(
    ! [A_608,A_609] :
      ( v3_pre_topc('#skF_1'(A_608,u1_struct_0(A_608),A_609),A_608)
      | ~ v2_tex_2(u1_struct_0(A_608),A_608)
      | ~ l1_pre_topc(A_608)
      | ~ r1_tarski(A_609,u1_struct_0(A_608)) ) ),
    inference(resolution,[status(thm)],[c_95,c_7513])).

tff(c_7558,plain,(
    ! [A_609] :
      ( v3_pre_topc('#skF_1'('#skF_9','#skF_10',A_609),'#skF_9')
      | ~ v2_tex_2(u1_struct_0('#skF_9'),'#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ r1_tarski(A_609,u1_struct_0('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_7547])).

tff(c_7567,plain,(
    ! [A_610] :
      ( v3_pre_topc('#skF_1'('#skF_9','#skF_10',A_610),'#skF_9')
      | ~ r1_tarski(A_610,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_88,c_182,c_1561,c_7558])).

tff(c_4574,plain,(
    ! [B_416,A_417] :
      ( v4_pre_topc(B_416,A_417)
      | ~ v3_pre_topc(B_416,A_417)
      | ~ m1_subset_1(B_416,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ v3_tdlat_3(A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4580,plain,(
    ! [B_416] :
      ( v4_pre_topc(B_416,'#skF_9')
      | ~ v3_pre_topc(B_416,'#skF_9')
      | ~ m1_subset_1(B_416,k1_zfmisc_1('#skF_10'))
      | ~ v3_tdlat_3('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_4574])).

tff(c_4606,plain,(
    ! [B_418] :
      ( v4_pre_topc(B_418,'#skF_9')
      | ~ v3_pre_topc(B_418,'#skF_9')
      | ~ m1_subset_1(B_418,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_90,c_4580])).

tff(c_4635,plain,(
    ! [A_419] :
      ( v4_pre_topc(A_419,'#skF_9')
      | ~ v3_pre_topc(A_419,'#skF_9')
      | ~ r1_tarski(A_419,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_8,c_4606])).

tff(c_3892,plain,(
    ! [A_3] :
      ( k2_pre_topc('#skF_9',A_3) = A_3
      | ~ v4_pre_topc(A_3,'#skF_9')
      | ~ r1_tarski(A_3,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_8,c_3879])).

tff(c_4688,plain,(
    ! [A_419] :
      ( k2_pre_topc('#skF_9',A_419) = A_419
      | ~ v3_pre_topc(A_419,'#skF_9')
      | ~ r1_tarski(A_419,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4635,c_3892])).

tff(c_7586,plain,(
    ! [A_614] :
      ( k2_pre_topc('#skF_9','#skF_1'('#skF_9','#skF_10',A_614)) = '#skF_1'('#skF_9','#skF_10',A_614)
      | ~ r1_tarski('#skF_1'('#skF_9','#skF_10',A_614),'#skF_10')
      | ~ r1_tarski(A_614,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_7567,c_4688])).

tff(c_7590,plain,(
    ! [C_568] :
      ( k2_pre_topc('#skF_9','#skF_1'('#skF_9','#skF_10',C_568)) = '#skF_1'('#skF_9','#skF_10',C_568)
      | ~ r1_tarski(C_568,'#skF_10')
      | ~ m1_subset_1(C_568,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2('#skF_10','#skF_9')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_6844,c_7586])).

tff(c_7594,plain,(
    ! [C_615] :
      ( k2_pre_topc('#skF_9','#skF_1'('#skF_9','#skF_10',C_615)) = '#skF_1'('#skF_9','#skF_10',C_615)
      | ~ r1_tarski(C_615,'#skF_10')
      | ~ m1_subset_1(C_615,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_182,c_7590])).

tff(c_7757,plain,(
    ! [A_619] :
      ( k2_pre_topc('#skF_9','#skF_1'('#skF_9','#skF_10',A_619)) = '#skF_1'('#skF_9','#skF_10',A_619)
      | ~ r1_tarski(A_619,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_8,c_7594])).

tff(c_7207,plain,(
    ! [A_591,B_592,C_593] :
      ( k9_subset_1(u1_struct_0(A_591),B_592,k2_pre_topc(A_591,C_593)) = C_593
      | ~ r1_tarski(C_593,B_592)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(u1_struct_0(A_591)))
      | ~ v2_tex_2(B_592,A_591)
      | ~ m1_subset_1(B_592,k1_zfmisc_1(u1_struct_0(A_591)))
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591)
      | v2_struct_0(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7217,plain,(
    ! [B_592,C_593] :
      ( k9_subset_1(u1_struct_0('#skF_9'),B_592,k2_pre_topc('#skF_9',C_593)) = C_593
      | ~ r1_tarski(C_593,B_592)
      | ~ m1_subset_1(C_593,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_592,'#skF_9')
      | ~ m1_subset_1(B_592,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_7207])).

tff(c_7235,plain,(
    ! [B_592,C_593] :
      ( k9_subset_1('#skF_10',B_592,k2_pre_topc('#skF_9',C_593)) = C_593
      | ~ r1_tarski(C_593,B_592)
      | ~ m1_subset_1(C_593,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_592,'#skF_9')
      | ~ m1_subset_1(B_592,k1_zfmisc_1('#skF_10'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_1561,c_1561,c_7217])).

tff(c_7265,plain,(
    ! [B_595,C_596] :
      ( k9_subset_1('#skF_10',B_595,k2_pre_topc('#skF_9',C_596)) = C_596
      | ~ r1_tarski(C_596,B_595)
      | ~ m1_subset_1(C_596,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2(B_595,'#skF_9')
      | ~ m1_subset_1(B_595,k1_zfmisc_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_7235])).

tff(c_7389,plain,(
    ! [B_600,A_601] :
      ( k9_subset_1('#skF_10',B_600,k2_pre_topc('#skF_9',A_601)) = A_601
      | ~ r1_tarski(A_601,B_600)
      | ~ v2_tex_2(B_600,'#skF_9')
      | ~ m1_subset_1(B_600,k1_zfmisc_1('#skF_10'))
      | ~ r1_tarski(A_601,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_8,c_7265])).

tff(c_7405,plain,(
    ! [A_601] :
      ( k9_subset_1('#skF_10','#skF_10',k2_pre_topc('#skF_9',A_601)) = A_601
      | ~ v2_tex_2('#skF_10','#skF_9')
      | ~ r1_tarski(A_601,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_95,c_7389])).

tff(c_7414,plain,(
    ! [A_601] :
      ( k9_subset_1('#skF_10','#skF_10',k2_pre_topc('#skF_9',A_601)) = A_601
      | ~ r1_tarski(A_601,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_7405])).

tff(c_7789,plain,(
    ! [A_620] :
      ( k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10',A_620)) = '#skF_1'('#skF_9','#skF_10',A_620)
      | ~ r1_tarski('#skF_1'('#skF_9','#skF_10',A_620),'#skF_10')
      | ~ r1_tarski(A_620,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7757,c_7414])).

tff(c_7796,plain,(
    ! [C_568] :
      ( k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10',C_568)) = '#skF_1'('#skF_9','#skF_10',C_568)
      | ~ r1_tarski(C_568,'#skF_10')
      | ~ m1_subset_1(C_568,k1_zfmisc_1('#skF_10'))
      | ~ v2_tex_2('#skF_10','#skF_9')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_6844,c_7789])).

tff(c_7802,plain,(
    ! [C_621] :
      ( k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10',C_621)) = '#skF_1'('#skF_9','#skF_10',C_621)
      | ~ r1_tarski(C_621,'#skF_10')
      | ~ m1_subset_1(C_621,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_182,c_7796])).

tff(c_7817,plain,
    ( k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9'))) = '#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9'))
    | ~ r1_tarski('#skF_4'('#skF_9'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_3820,c_7802])).

tff(c_7832,plain,(
    k9_subset_1('#skF_10','#skF_10','#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9'))) = '#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_7817])).

tff(c_7995,plain,
    ( '#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9')) = '#skF_4'('#skF_9')
    | ~ r1_tarski('#skF_4'('#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_7986,c_7832])).

tff(c_8020,plain,(
    '#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9')) = '#skF_4'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_7995])).

tff(c_7609,plain,
    ( k2_pre_topc('#skF_9','#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9'))) = '#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9'))
    | ~ r1_tarski('#skF_4'('#skF_9'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_3820,c_7594])).

tff(c_7624,plain,(
    k2_pre_topc('#skF_9','#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9'))) = '#skF_1'('#skF_9','#skF_10','#skF_4'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3817,c_7609])).

tff(c_8035,plain,(
    k2_pre_topc('#skF_9','#skF_4'('#skF_9')) = '#skF_4'('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8020,c_8020,c_7624])).

tff(c_8037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4146,c_8035])).

tff(c_8039,plain,(
    v4_pre_topc('#skF_4'('#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_3891])).

tff(c_8619,plain,(
    ! [B_670,A_671] :
      ( v3_pre_topc(B_670,A_671)
      | ~ v4_pre_topc(B_670,A_671)
      | ~ m1_subset_1(B_670,k1_zfmisc_1(u1_struct_0(A_671)))
      | ~ v3_tdlat_3(A_671)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8625,plain,(
    ! [B_670] :
      ( v3_pre_topc(B_670,'#skF_9')
      | ~ v4_pre_topc(B_670,'#skF_9')
      | ~ m1_subset_1(B_670,k1_zfmisc_1('#skF_10'))
      | ~ v3_tdlat_3('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_8619])).

tff(c_8651,plain,(
    ! [B_672] :
      ( v3_pre_topc(B_672,'#skF_9')
      | ~ v4_pre_topc(B_672,'#skF_9')
      | ~ m1_subset_1(B_672,k1_zfmisc_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_90,c_8625])).

tff(c_8657,plain,
    ( v3_pre_topc('#skF_4'('#skF_9'),'#skF_9')
    | ~ v4_pre_topc('#skF_4'('#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_3820,c_8651])).

tff(c_8669,plain,(
    v3_pre_topc('#skF_4'('#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8039,c_8657])).

tff(c_42,plain,(
    ! [A_46] :
      ( ~ v3_pre_topc('#skF_4'(A_46),A_46)
      | v1_tdlat_3(A_46)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8676,plain,
    ( v1_tdlat_3('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_8669,c_42])).

tff(c_8679,plain,(
    v1_tdlat_3('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_8676])).

tff(c_8681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3818,c_8679])).

tff(c_8683,plain,(
    ~ v3_pre_topc('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_8682,plain,(
    v4_pre_topc('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_9231,plain,(
    ! [B_737,A_738] :
      ( v3_pre_topc(B_737,A_738)
      | ~ v4_pre_topc(B_737,A_738)
      | ~ m1_subset_1(B_737,k1_zfmisc_1(u1_struct_0(A_738)))
      | ~ v3_tdlat_3(A_738)
      | ~ l1_pre_topc(A_738)
      | ~ v2_pre_topc(A_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9247,plain,
    ( v3_pre_topc('#skF_10','#skF_9')
    | ~ v4_pre_topc('#skF_10','#skF_9')
    | ~ v3_tdlat_3('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_9231])).

tff(c_9258,plain,(
    v3_pre_topc('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_90,c_8682,c_9247])).

tff(c_9260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8683,c_9258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.38/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.38/2.84  
% 8.38/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.38/2.84  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_5 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_6
% 8.38/2.84  
% 8.38/2.84  %Foreground sorts:
% 8.38/2.84  
% 8.38/2.84  
% 8.38/2.84  %Background operators:
% 8.38/2.84  
% 8.38/2.84  
% 8.38/2.84  %Foreground operators:
% 8.38/2.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.38/2.84  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.38/2.84  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.38/2.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.38/2.84  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.38/2.84  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.38/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.38/2.84  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 8.38/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.38/2.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.38/2.84  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 8.38/2.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.38/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.38/2.84  tff('#skF_10', type, '#skF_10': $i).
% 8.38/2.84  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.38/2.84  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 8.38/2.84  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.38/2.84  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.38/2.84  tff('#skF_9', type, '#skF_9': $i).
% 8.38/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.38/2.84  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 8.38/2.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.38/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.38/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.38/2.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.38/2.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.38/2.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.38/2.84  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.38/2.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.38/2.84  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.38/2.84  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.38/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.38/2.84  
% 8.38/2.87  tff(f_212, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 8.38/2.87  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.38/2.87  tff(f_125, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tdlat_3)).
% 8.38/2.87  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 8.38/2.87  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 8.38/2.87  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.38/2.87  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.38/2.87  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => ((![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k1_tarski(C)) => v3_pre_topc(B, A)))))) => v1_tdlat_3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tdlat_3)).
% 8.38/2.87  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.38/2.87  tff(f_190, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 8.38/2.87  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 8.38/2.87  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 8.38/2.87  tff(f_157, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 8.38/2.87  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 8.38/2.87  tff(c_82, plain, (v3_tex_2('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_94, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_88, plain, (l1_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_86, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_209, plain, (![A_101, B_102]: (k2_pre_topc(A_101, B_102)=B_102 | ~v4_pre_topc(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.38/2.87  tff(c_225, plain, (k2_pre_topc('#skF_9', '#skF_10')='#skF_10' | ~v4_pre_topc('#skF_10', '#skF_9') | ~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_86, c_209])).
% 8.38/2.87  tff(c_236, plain, (k2_pre_topc('#skF_9', '#skF_10')='#skF_10' | ~v4_pre_topc('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_225])).
% 8.38/2.87  tff(c_238, plain, (~v4_pre_topc('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_236])).
% 8.38/2.87  tff(c_92, plain, (v2_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_90, plain, (v3_tdlat_3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_84, plain, (v4_pre_topc('#skF_10', '#skF_9') | v3_pre_topc('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_106, plain, (v3_pre_topc('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_84])).
% 8.38/2.87  tff(c_611, plain, (![B_138, A_139]: (v4_pre_topc(B_138, A_139) | ~v3_pre_topc(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~v3_tdlat_3(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.38/2.87  tff(c_627, plain, (v4_pre_topc('#skF_10', '#skF_9') | ~v3_pre_topc('#skF_10', '#skF_9') | ~v3_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_86, c_611])).
% 8.38/2.87  tff(c_638, plain, (v4_pre_topc('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_90, c_106, c_627])).
% 8.38/2.87  tff(c_640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_638])).
% 8.38/2.87  tff(c_641, plain, (k2_pre_topc('#skF_9', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_236])).
% 8.38/2.87  tff(c_648, plain, (![B_141, A_142]: (v1_tops_1(B_141, A_142) | k2_pre_topc(A_142, B_141)!=u1_struct_0(A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.38/2.87  tff(c_664, plain, (v1_tops_1('#skF_10', '#skF_9') | k2_pre_topc('#skF_9', '#skF_10')!=u1_struct_0('#skF_9') | ~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_86, c_648])).
% 8.38/2.87  tff(c_675, plain, (v1_tops_1('#skF_10', '#skF_9') | u1_struct_0('#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_641, c_664])).
% 8.38/2.87  tff(c_677, plain, (u1_struct_0('#skF_9')!='#skF_10'), inference(splitLeft, [status(thm)], [c_675])).
% 8.38/2.87  tff(c_727, plain, (![A_148, B_149]: (k2_pre_topc(A_148, B_149)=u1_struct_0(A_148) | ~v1_tops_1(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.38/2.87  tff(c_743, plain, (k2_pre_topc('#skF_9', '#skF_10')=u1_struct_0('#skF_9') | ~v1_tops_1('#skF_10', '#skF_9') | ~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_86, c_727])).
% 8.38/2.87  tff(c_754, plain, (u1_struct_0('#skF_9')='#skF_10' | ~v1_tops_1('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_641, c_743])).
% 8.38/2.87  tff(c_755, plain, (~v1_tops_1('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_677, c_754])).
% 8.38/2.87  tff(c_1522, plain, (![B_217, A_218]: (v1_tops_1(B_217, A_218) | ~v3_tex_2(B_217, A_218) | ~v3_pre_topc(B_217, A_218) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.38/2.87  tff(c_1544, plain, (v1_tops_1('#skF_10', '#skF_9') | ~v3_tex_2('#skF_10', '#skF_9') | ~v3_pre_topc('#skF_10', '#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_86, c_1522])).
% 8.38/2.87  tff(c_1557, plain, (v1_tops_1('#skF_10', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_106, c_82, c_1544])).
% 8.38/2.87  tff(c_1559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_755, c_1557])).
% 8.38/2.87  tff(c_1561, plain, (u1_struct_0('#skF_9')='#skF_10'), inference(splitRight, [status(thm)], [c_675])).
% 8.38/2.87  tff(c_80, plain, (v1_subset_1('#skF_10', u1_struct_0('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 8.38/2.87  tff(c_1564, plain, (v1_subset_1('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_80])).
% 8.38/2.87  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.38/2.87  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.38/2.87  tff(c_95, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 8.38/2.87  tff(c_143, plain, (![A_92]: (m1_subset_1('#skF_4'(A_92), k1_zfmisc_1(u1_struct_0(A_92))) | v1_tdlat_3(A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.38/2.87  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.38/2.87  tff(c_147, plain, (![A_92]: (r1_tarski('#skF_4'(A_92), u1_struct_0(A_92)) | v1_tdlat_3(A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(resolution, [status(thm)], [c_143, c_6])).
% 8.38/2.87  tff(c_1591, plain, (r1_tarski('#skF_4'('#skF_9'), '#skF_10') | v1_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1561, c_147])).
% 8.38/2.87  tff(c_1624, plain, (r1_tarski('#skF_4'('#skF_9'), '#skF_10') | v1_tdlat_3('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_1591])).
% 8.38/2.87  tff(c_1636, plain, (v1_tdlat_3('#skF_9')), inference(splitLeft, [status(thm)], [c_1624])).
% 8.38/2.87  tff(c_3758, plain, (![B_359, A_360]: (~v1_subset_1(B_359, u1_struct_0(A_360)) | ~v3_tex_2(B_359, A_360) | ~m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0(A_360))) | ~l1_pre_topc(A_360) | ~v1_tdlat_3(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_190])).
% 8.38/2.87  tff(c_3767, plain, (![B_359]: (~v1_subset_1(B_359, u1_struct_0('#skF_9')) | ~v3_tex_2(B_359, '#skF_9') | ~m1_subset_1(B_359, k1_zfmisc_1('#skF_10')) | ~l1_pre_topc('#skF_9') | ~v1_tdlat_3('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_3758])).
% 8.38/2.87  tff(c_3788, plain, (![B_359]: (~v1_subset_1(B_359, '#skF_10') | ~v3_tex_2(B_359, '#skF_9') | ~m1_subset_1(B_359, k1_zfmisc_1('#skF_10')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1636, c_88, c_1561, c_3767])).
% 8.38/2.87  tff(c_3795, plain, (![B_361]: (~v1_subset_1(B_361, '#skF_10') | ~v3_tex_2(B_361, '#skF_9') | ~m1_subset_1(B_361, k1_zfmisc_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_94, c_3788])).
% 8.38/2.87  tff(c_3809, plain, (~v1_subset_1('#skF_10', '#skF_10') | ~v3_tex_2('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_95, c_3795])).
% 8.38/2.87  tff(c_3816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1564, c_3809])).
% 8.38/2.87  tff(c_3818, plain, (~v1_tdlat_3('#skF_9')), inference(splitRight, [status(thm)], [c_1624])).
% 8.38/2.87  tff(c_48, plain, (![A_46]: (m1_subset_1('#skF_4'(A_46), k1_zfmisc_1(u1_struct_0(A_46))) | v1_tdlat_3(A_46) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.38/2.87  tff(c_1597, plain, (m1_subset_1('#skF_4'('#skF_9'), k1_zfmisc_1('#skF_10')) | v1_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1561, c_48])).
% 8.38/2.87  tff(c_1628, plain, (m1_subset_1('#skF_4'('#skF_9'), k1_zfmisc_1('#skF_10')) | v1_tdlat_3('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_1597])).
% 8.38/2.87  tff(c_3820, plain, (m1_subset_1('#skF_4'('#skF_9'), k1_zfmisc_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_3818, c_1628])).
% 8.38/2.87  tff(c_12, plain, (![A_5, B_7]: (k2_pre_topc(A_5, B_7)=B_7 | ~v4_pre_topc(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.38/2.87  tff(c_1576, plain, (![B_7]: (k2_pre_topc('#skF_9', B_7)=B_7 | ~v4_pre_topc(B_7, '#skF_9') | ~m1_subset_1(B_7, k1_zfmisc_1('#skF_10')) | ~l1_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_12])).
% 8.38/2.87  tff(c_3879, plain, (![B_366]: (k2_pre_topc('#skF_9', B_366)=B_366 | ~v4_pre_topc(B_366, '#skF_9') | ~m1_subset_1(B_366, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1576])).
% 8.38/2.87  tff(c_3891, plain, (k2_pre_topc('#skF_9', '#skF_4'('#skF_9'))='#skF_4'('#skF_9') | ~v4_pre_topc('#skF_4'('#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_3820, c_3879])).
% 8.38/2.87  tff(c_3896, plain, (~v4_pre_topc('#skF_4'('#skF_9'), '#skF_9')), inference(splitLeft, [status(thm)], [c_3891])).
% 8.38/2.87  tff(c_4104, plain, (![B_383, A_384]: (v4_pre_topc(B_383, A_384) | k2_pre_topc(A_384, B_383)!=B_383 | ~v2_pre_topc(A_384) | ~m1_subset_1(B_383, k1_zfmisc_1(u1_struct_0(A_384))) | ~l1_pre_topc(A_384))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.38/2.87  tff(c_4107, plain, (![B_383]: (v4_pre_topc(B_383, '#skF_9') | k2_pre_topc('#skF_9', B_383)!=B_383 | ~v2_pre_topc('#skF_9') | ~m1_subset_1(B_383, k1_zfmisc_1('#skF_10')) | ~l1_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_4104])).
% 8.38/2.87  tff(c_4132, plain, (![B_385]: (v4_pre_topc(B_385, '#skF_9') | k2_pre_topc('#skF_9', B_385)!=B_385 | ~m1_subset_1(B_385, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_92, c_4107])).
% 8.38/2.87  tff(c_4135, plain, (v4_pre_topc('#skF_4'('#skF_9'), '#skF_9') | k2_pre_topc('#skF_9', '#skF_4'('#skF_9'))!='#skF_4'('#skF_9')), inference(resolution, [status(thm)], [c_3820, c_4132])).
% 8.38/2.87  tff(c_4146, plain, (k2_pre_topc('#skF_9', '#skF_4'('#skF_9'))!='#skF_4'('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_3896, c_4135])).
% 8.38/2.87  tff(c_3817, plain, (r1_tarski('#skF_4'('#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_1624])).
% 8.38/2.87  tff(c_155, plain, (![B_96, A_97]: (v2_tex_2(B_96, A_97) | ~v3_tex_2(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.38/2.87  tff(c_171, plain, (v2_tex_2('#skF_10', '#skF_9') | ~v3_tex_2('#skF_10', '#skF_9') | ~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_86, c_155])).
% 8.38/2.87  tff(c_182, plain, (v2_tex_2('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_171])).
% 8.38/2.87  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.38/2.87  tff(c_6967, plain, (![A_581, B_582, C_583]: (k9_subset_1(u1_struct_0(A_581), B_582, '#skF_1'(A_581, B_582, C_583))=C_583 | ~r1_tarski(C_583, B_582) | ~m1_subset_1(C_583, k1_zfmisc_1(u1_struct_0(A_581))) | ~v2_tex_2(B_582, A_581) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_581))) | ~l1_pre_topc(A_581))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.38/2.87  tff(c_6977, plain, (![B_582, C_583]: (k9_subset_1(u1_struct_0('#skF_9'), B_582, '#skF_1'('#skF_9', B_582, C_583))=C_583 | ~r1_tarski(C_583, B_582) | ~m1_subset_1(C_583, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_582, '#skF_9') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_9'))) | ~l1_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_6967])).
% 8.38/2.87  tff(c_7149, plain, (![B_588, C_589]: (k9_subset_1('#skF_10', B_588, '#skF_1'('#skF_9', B_588, C_589))=C_589 | ~r1_tarski(C_589, B_588) | ~m1_subset_1(C_589, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_588, '#skF_9') | ~m1_subset_1(B_588, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1561, c_1561, c_6977])).
% 8.38/2.87  tff(c_7922, plain, (![B_625, A_626]: (k9_subset_1('#skF_10', B_625, '#skF_1'('#skF_9', B_625, A_626))=A_626 | ~r1_tarski(A_626, B_625) | ~v2_tex_2(B_625, '#skF_9') | ~m1_subset_1(B_625, k1_zfmisc_1('#skF_10')) | ~r1_tarski(A_626, '#skF_10'))), inference(resolution, [status(thm)], [c_8, c_7149])).
% 8.38/2.87  tff(c_7938, plain, (![A_626]: (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', A_626))=A_626 | ~v2_tex_2('#skF_10', '#skF_9') | ~r1_tarski(A_626, '#skF_10'))), inference(resolution, [status(thm)], [c_95, c_7922])).
% 8.38/2.87  tff(c_7986, plain, (![A_628]: (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', A_628))=A_628 | ~r1_tarski(A_628, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_7938])).
% 8.38/2.87  tff(c_6735, plain, (![A_564, B_565, C_566]: (m1_subset_1('#skF_1'(A_564, B_565, C_566), k1_zfmisc_1(u1_struct_0(A_564))) | ~r1_tarski(C_566, B_565) | ~m1_subset_1(C_566, k1_zfmisc_1(u1_struct_0(A_564))) | ~v2_tex_2(B_565, A_564) | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~l1_pre_topc(A_564))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.38/2.87  tff(c_6784, plain, (![B_565, C_566]: (m1_subset_1('#skF_1'('#skF_9', B_565, C_566), k1_zfmisc_1('#skF_10')) | ~r1_tarski(C_566, B_565) | ~m1_subset_1(C_566, k1_zfmisc_1(u1_struct_0('#skF_9'))) | ~v2_tex_2(B_565, '#skF_9') | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0('#skF_9'))) | ~l1_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_6735])).
% 8.38/2.87  tff(c_6804, plain, (![B_567, C_568]: (m1_subset_1('#skF_1'('#skF_9', B_567, C_568), k1_zfmisc_1('#skF_10')) | ~r1_tarski(C_568, B_567) | ~m1_subset_1(C_568, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_567, '#skF_9') | ~m1_subset_1(B_567, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1561, c_1561, c_6784])).
% 8.38/2.87  tff(c_6844, plain, (![B_567, C_568]: (r1_tarski('#skF_1'('#skF_9', B_567, C_568), '#skF_10') | ~r1_tarski(C_568, B_567) | ~m1_subset_1(C_568, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_567, '#skF_9') | ~m1_subset_1(B_567, k1_zfmisc_1('#skF_10')))), inference(resolution, [status(thm)], [c_6804, c_6])).
% 8.38/2.87  tff(c_6482, plain, (![A_533, B_534, C_535]: (v3_pre_topc('#skF_1'(A_533, B_534, C_535), A_533) | ~r1_tarski(C_535, B_534) | ~m1_subset_1(C_535, k1_zfmisc_1(u1_struct_0(A_533))) | ~v2_tex_2(B_534, A_533) | ~m1_subset_1(B_534, k1_zfmisc_1(u1_struct_0(A_533))) | ~l1_pre_topc(A_533))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.38/2.87  tff(c_7513, plain, (![A_605, B_606, A_607]: (v3_pre_topc('#skF_1'(A_605, B_606, A_607), A_605) | ~r1_tarski(A_607, B_606) | ~v2_tex_2(B_606, A_605) | ~m1_subset_1(B_606, k1_zfmisc_1(u1_struct_0(A_605))) | ~l1_pre_topc(A_605) | ~r1_tarski(A_607, u1_struct_0(A_605)))), inference(resolution, [status(thm)], [c_8, c_6482])).
% 8.38/2.87  tff(c_7547, plain, (![A_608, A_609]: (v3_pre_topc('#skF_1'(A_608, u1_struct_0(A_608), A_609), A_608) | ~v2_tex_2(u1_struct_0(A_608), A_608) | ~l1_pre_topc(A_608) | ~r1_tarski(A_609, u1_struct_0(A_608)))), inference(resolution, [status(thm)], [c_95, c_7513])).
% 8.38/2.87  tff(c_7558, plain, (![A_609]: (v3_pre_topc('#skF_1'('#skF_9', '#skF_10', A_609), '#skF_9') | ~v2_tex_2(u1_struct_0('#skF_9'), '#skF_9') | ~l1_pre_topc('#skF_9') | ~r1_tarski(A_609, u1_struct_0('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_7547])).
% 8.38/2.87  tff(c_7567, plain, (![A_610]: (v3_pre_topc('#skF_1'('#skF_9', '#skF_10', A_610), '#skF_9') | ~r1_tarski(A_610, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_88, c_182, c_1561, c_7558])).
% 8.38/2.87  tff(c_4574, plain, (![B_416, A_417]: (v4_pre_topc(B_416, A_417) | ~v3_pre_topc(B_416, A_417) | ~m1_subset_1(B_416, k1_zfmisc_1(u1_struct_0(A_417))) | ~v3_tdlat_3(A_417) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.38/2.87  tff(c_4580, plain, (![B_416]: (v4_pre_topc(B_416, '#skF_9') | ~v3_pre_topc(B_416, '#skF_9') | ~m1_subset_1(B_416, k1_zfmisc_1('#skF_10')) | ~v3_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_4574])).
% 8.38/2.87  tff(c_4606, plain, (![B_418]: (v4_pre_topc(B_418, '#skF_9') | ~v3_pre_topc(B_418, '#skF_9') | ~m1_subset_1(B_418, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_90, c_4580])).
% 8.38/2.87  tff(c_4635, plain, (![A_419]: (v4_pre_topc(A_419, '#skF_9') | ~v3_pre_topc(A_419, '#skF_9') | ~r1_tarski(A_419, '#skF_10'))), inference(resolution, [status(thm)], [c_8, c_4606])).
% 8.38/2.87  tff(c_3892, plain, (![A_3]: (k2_pre_topc('#skF_9', A_3)=A_3 | ~v4_pre_topc(A_3, '#skF_9') | ~r1_tarski(A_3, '#skF_10'))), inference(resolution, [status(thm)], [c_8, c_3879])).
% 8.38/2.87  tff(c_4688, plain, (![A_419]: (k2_pre_topc('#skF_9', A_419)=A_419 | ~v3_pre_topc(A_419, '#skF_9') | ~r1_tarski(A_419, '#skF_10'))), inference(resolution, [status(thm)], [c_4635, c_3892])).
% 8.38/2.87  tff(c_7586, plain, (![A_614]: (k2_pre_topc('#skF_9', '#skF_1'('#skF_9', '#skF_10', A_614))='#skF_1'('#skF_9', '#skF_10', A_614) | ~r1_tarski('#skF_1'('#skF_9', '#skF_10', A_614), '#skF_10') | ~r1_tarski(A_614, '#skF_10'))), inference(resolution, [status(thm)], [c_7567, c_4688])).
% 8.38/2.87  tff(c_7590, plain, (![C_568]: (k2_pre_topc('#skF_9', '#skF_1'('#skF_9', '#skF_10', C_568))='#skF_1'('#skF_9', '#skF_10', C_568) | ~r1_tarski(C_568, '#skF_10') | ~m1_subset_1(C_568, k1_zfmisc_1('#skF_10')) | ~v2_tex_2('#skF_10', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_10')))), inference(resolution, [status(thm)], [c_6844, c_7586])).
% 8.38/2.87  tff(c_7594, plain, (![C_615]: (k2_pre_topc('#skF_9', '#skF_1'('#skF_9', '#skF_10', C_615))='#skF_1'('#skF_9', '#skF_10', C_615) | ~r1_tarski(C_615, '#skF_10') | ~m1_subset_1(C_615, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_182, c_7590])).
% 8.38/2.87  tff(c_7757, plain, (![A_619]: (k2_pre_topc('#skF_9', '#skF_1'('#skF_9', '#skF_10', A_619))='#skF_1'('#skF_9', '#skF_10', A_619) | ~r1_tarski(A_619, '#skF_10'))), inference(resolution, [status(thm)], [c_8, c_7594])).
% 8.38/2.87  tff(c_7207, plain, (![A_591, B_592, C_593]: (k9_subset_1(u1_struct_0(A_591), B_592, k2_pre_topc(A_591, C_593))=C_593 | ~r1_tarski(C_593, B_592) | ~m1_subset_1(C_593, k1_zfmisc_1(u1_struct_0(A_591))) | ~v2_tex_2(B_592, A_591) | ~m1_subset_1(B_592, k1_zfmisc_1(u1_struct_0(A_591))) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591) | v2_struct_0(A_591))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.38/2.87  tff(c_7217, plain, (![B_592, C_593]: (k9_subset_1(u1_struct_0('#skF_9'), B_592, k2_pre_topc('#skF_9', C_593))=C_593 | ~r1_tarski(C_593, B_592) | ~m1_subset_1(C_593, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_592, '#skF_9') | ~m1_subset_1(B_592, k1_zfmisc_1(u1_struct_0('#skF_9'))) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_7207])).
% 8.38/2.87  tff(c_7235, plain, (![B_592, C_593]: (k9_subset_1('#skF_10', B_592, k2_pre_topc('#skF_9', C_593))=C_593 | ~r1_tarski(C_593, B_592) | ~m1_subset_1(C_593, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_592, '#skF_9') | ~m1_subset_1(B_592, k1_zfmisc_1('#skF_10')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_1561, c_1561, c_7217])).
% 8.38/2.87  tff(c_7265, plain, (![B_595, C_596]: (k9_subset_1('#skF_10', B_595, k2_pre_topc('#skF_9', C_596))=C_596 | ~r1_tarski(C_596, B_595) | ~m1_subset_1(C_596, k1_zfmisc_1('#skF_10')) | ~v2_tex_2(B_595, '#skF_9') | ~m1_subset_1(B_595, k1_zfmisc_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_94, c_7235])).
% 8.38/2.87  tff(c_7389, plain, (![B_600, A_601]: (k9_subset_1('#skF_10', B_600, k2_pre_topc('#skF_9', A_601))=A_601 | ~r1_tarski(A_601, B_600) | ~v2_tex_2(B_600, '#skF_9') | ~m1_subset_1(B_600, k1_zfmisc_1('#skF_10')) | ~r1_tarski(A_601, '#skF_10'))), inference(resolution, [status(thm)], [c_8, c_7265])).
% 8.38/2.87  tff(c_7405, plain, (![A_601]: (k9_subset_1('#skF_10', '#skF_10', k2_pre_topc('#skF_9', A_601))=A_601 | ~v2_tex_2('#skF_10', '#skF_9') | ~r1_tarski(A_601, '#skF_10'))), inference(resolution, [status(thm)], [c_95, c_7389])).
% 8.38/2.87  tff(c_7414, plain, (![A_601]: (k9_subset_1('#skF_10', '#skF_10', k2_pre_topc('#skF_9', A_601))=A_601 | ~r1_tarski(A_601, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_7405])).
% 8.38/2.87  tff(c_7789, plain, (![A_620]: (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', A_620))='#skF_1'('#skF_9', '#skF_10', A_620) | ~r1_tarski('#skF_1'('#skF_9', '#skF_10', A_620), '#skF_10') | ~r1_tarski(A_620, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_7757, c_7414])).
% 8.38/2.87  tff(c_7796, plain, (![C_568]: (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', C_568))='#skF_1'('#skF_9', '#skF_10', C_568) | ~r1_tarski(C_568, '#skF_10') | ~m1_subset_1(C_568, k1_zfmisc_1('#skF_10')) | ~v2_tex_2('#skF_10', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_10')))), inference(resolution, [status(thm)], [c_6844, c_7789])).
% 8.38/2.87  tff(c_7802, plain, (![C_621]: (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', C_621))='#skF_1'('#skF_9', '#skF_10', C_621) | ~r1_tarski(C_621, '#skF_10') | ~m1_subset_1(C_621, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_182, c_7796])).
% 8.38/2.87  tff(c_7817, plain, (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9')))='#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9')) | ~r1_tarski('#skF_4'('#skF_9'), '#skF_10')), inference(resolution, [status(thm)], [c_3820, c_7802])).
% 8.38/2.87  tff(c_7832, plain, (k9_subset_1('#skF_10', '#skF_10', '#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9')))='#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_7817])).
% 8.38/2.87  tff(c_7995, plain, ('#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9'))='#skF_4'('#skF_9') | ~r1_tarski('#skF_4'('#skF_9'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_7986, c_7832])).
% 8.38/2.87  tff(c_8020, plain, ('#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9'))='#skF_4'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_7995])).
% 8.38/2.87  tff(c_7609, plain, (k2_pre_topc('#skF_9', '#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9')))='#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9')) | ~r1_tarski('#skF_4'('#skF_9'), '#skF_10')), inference(resolution, [status(thm)], [c_3820, c_7594])).
% 8.38/2.87  tff(c_7624, plain, (k2_pre_topc('#skF_9', '#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9')))='#skF_1'('#skF_9', '#skF_10', '#skF_4'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3817, c_7609])).
% 8.38/2.87  tff(c_8035, plain, (k2_pre_topc('#skF_9', '#skF_4'('#skF_9'))='#skF_4'('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8020, c_8020, c_7624])).
% 8.38/2.87  tff(c_8037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4146, c_8035])).
% 8.38/2.87  tff(c_8039, plain, (v4_pre_topc('#skF_4'('#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_3891])).
% 8.38/2.87  tff(c_8619, plain, (![B_670, A_671]: (v3_pre_topc(B_670, A_671) | ~v4_pre_topc(B_670, A_671) | ~m1_subset_1(B_670, k1_zfmisc_1(u1_struct_0(A_671))) | ~v3_tdlat_3(A_671) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.38/2.87  tff(c_8625, plain, (![B_670]: (v3_pre_topc(B_670, '#skF_9') | ~v4_pre_topc(B_670, '#skF_9') | ~m1_subset_1(B_670, k1_zfmisc_1('#skF_10')) | ~v3_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_8619])).
% 8.38/2.87  tff(c_8651, plain, (![B_672]: (v3_pre_topc(B_672, '#skF_9') | ~v4_pre_topc(B_672, '#skF_9') | ~m1_subset_1(B_672, k1_zfmisc_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_90, c_8625])).
% 8.38/2.87  tff(c_8657, plain, (v3_pre_topc('#skF_4'('#skF_9'), '#skF_9') | ~v4_pre_topc('#skF_4'('#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_3820, c_8651])).
% 8.38/2.87  tff(c_8669, plain, (v3_pre_topc('#skF_4'('#skF_9'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8039, c_8657])).
% 8.38/2.87  tff(c_42, plain, (![A_46]: (~v3_pre_topc('#skF_4'(A_46), A_46) | v1_tdlat_3(A_46) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.38/2.87  tff(c_8676, plain, (v1_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_8669, c_42])).
% 8.38/2.87  tff(c_8679, plain, (v1_tdlat_3('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_8676])).
% 8.38/2.87  tff(c_8681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3818, c_8679])).
% 8.38/2.87  tff(c_8683, plain, (~v3_pre_topc('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_84])).
% 8.38/2.87  tff(c_8682, plain, (v4_pre_topc('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_84])).
% 8.38/2.87  tff(c_9231, plain, (![B_737, A_738]: (v3_pre_topc(B_737, A_738) | ~v4_pre_topc(B_737, A_738) | ~m1_subset_1(B_737, k1_zfmisc_1(u1_struct_0(A_738))) | ~v3_tdlat_3(A_738) | ~l1_pre_topc(A_738) | ~v2_pre_topc(A_738))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.38/2.87  tff(c_9247, plain, (v3_pre_topc('#skF_10', '#skF_9') | ~v4_pre_topc('#skF_10', '#skF_9') | ~v3_tdlat_3('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_86, c_9231])).
% 8.38/2.87  tff(c_9258, plain, (v3_pre_topc('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_90, c_8682, c_9247])).
% 8.38/2.87  tff(c_9260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8683, c_9258])).
% 8.38/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.38/2.87  
% 8.38/2.87  Inference rules
% 8.38/2.87  ----------------------
% 8.38/2.87  #Ref     : 0
% 8.38/2.87  #Sup     : 1866
% 8.38/2.87  #Fact    : 0
% 8.38/2.87  #Define  : 0
% 8.38/2.87  #Split   : 13
% 8.38/2.87  #Chain   : 0
% 8.38/2.87  #Close   : 0
% 8.38/2.87  
% 8.38/2.87  Ordering : KBO
% 8.38/2.87  
% 8.38/2.87  Simplification rules
% 8.38/2.87  ----------------------
% 8.38/2.87  #Subsume      : 324
% 8.38/2.87  #Demod        : 2252
% 8.38/2.87  #Tautology    : 532
% 8.38/2.87  #SimpNegUnit  : 84
% 8.38/2.87  #BackRed      : 7
% 8.38/2.87  
% 8.38/2.87  #Partial instantiations: 0
% 8.38/2.87  #Strategies tried      : 1
% 8.38/2.87  
% 8.38/2.87  Timing (in seconds)
% 8.38/2.87  ----------------------
% 8.38/2.87  Preprocessing        : 0.38
% 8.38/2.87  Parsing              : 0.19
% 8.38/2.87  CNF conversion       : 0.03
% 8.38/2.87  Main loop            : 1.67
% 8.38/2.87  Inferencing          : 0.61
% 8.38/2.87  Reduction            : 0.51
% 8.38/2.87  Demodulation         : 0.35
% 8.38/2.87  BG Simplification    : 0.07
% 8.38/2.87  Subsumption          : 0.34
% 8.38/2.87  Abstraction          : 0.08
% 8.38/2.87  MUC search           : 0.00
% 8.38/2.87  Cooper               : 0.00
% 8.38/2.87  Total                : 2.10
% 8.38/2.87  Index Insertion      : 0.00
% 8.38/2.87  Index Deletion       : 0.00
% 8.38/2.87  Index Matching       : 0.00
% 8.38/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
