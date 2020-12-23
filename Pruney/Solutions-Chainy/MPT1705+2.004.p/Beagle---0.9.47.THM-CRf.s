%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:24 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :  205 (1211 expanded)
%              Number of leaves         :   37 ( 434 expanded)
%              Depth                    :   15
%              Number of atoms          :  510 (4363 expanded)
%              Number of equality atoms :   16 ( 442 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_tsep_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_tsep_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_138,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(c_92,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_106,plain,
    ( v1_tsep_1('#skF_5','#skF_4')
    | m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_126,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_86,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_88,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_90,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_50,plain,(
    ! [A_7] :
      ( r2_hidden(u1_struct_0(A_7),u1_pre_topc(A_7))
      | ~ v2_pre_topc(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_3895,plain,(
    ! [B_285,A_286] :
      ( v3_pre_topc(B_285,A_286)
      | ~ r2_hidden(B_285,u1_pre_topc(A_286))
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3910,plain,(
    ! [A_287] :
      ( v3_pre_topc(u1_struct_0(A_287),A_287)
      | ~ r2_hidden(u1_struct_0(A_287),u1_pre_topc(A_287))
      | ~ l1_pre_topc(A_287) ) ),
    inference(resolution,[status(thm)],[c_113,c_3895])).

tff(c_3914,plain,(
    ! [A_7] :
      ( v3_pre_topc(u1_struct_0(A_7),A_7)
      | ~ v2_pre_topc(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_50,c_3910])).

tff(c_82,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_3992,plain,(
    ! [B_299,A_300] :
      ( v3_pre_topc(B_299,g1_pre_topc(u1_struct_0(A_300),u1_pre_topc(A_300)))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ v3_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3995,plain,(
    ! [B_299] :
      ( v3_pre_topc(B_299,'#skF_6')
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_299,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_3992])).

tff(c_3998,plain,(
    ! [B_301] :
      ( v3_pre_topc(B_301,'#skF_6')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_301,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_3995])).

tff(c_4015,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_3998])).

tff(c_4016,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4015])).

tff(c_4019,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3914,c_4016])).

tff(c_4023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_90,c_4019])).

tff(c_4025,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4015])).

tff(c_4329,plain,(
    ! [B_337,A_338] :
      ( m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_338),u1_pre_topc(A_338)))))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ v3_pre_topc(B_337,A_338)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4341,plain,(
    ! [B_337] :
      ( m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_337,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4329])).

tff(c_4347,plain,(
    ! [B_339] :
      ( m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_339,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4341])).

tff(c_4367,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_4347])).

tff(c_4380,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4025,c_4367])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4396,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4380,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4434,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4396,c_2])).

tff(c_4436,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4434])).

tff(c_84,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4827,plain,(
    ! [B_371,A_372] :
      ( v3_pre_topc(B_371,A_372)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_372),u1_pre_topc(A_372)))))
      | ~ v3_pre_topc(B_371,g1_pre_topc(u1_struct_0(A_372),u1_pre_topc(A_372)))
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4849,plain,(
    ! [B_371] :
      ( v3_pre_topc(B_371,'#skF_5')
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_371,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4827])).

tff(c_4862,plain,(
    ! [B_373] :
      ( v3_pre_topc(B_373,'#skF_5')
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_373,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_4849])).

tff(c_4907,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_4862])).

tff(c_4908,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4907])).

tff(c_4917,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_3914,c_4908])).

tff(c_4925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_4917])).

tff(c_4927,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4907])).

tff(c_5063,plain,(
    ! [B_380,A_381] :
      ( m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_381),u1_pre_topc(A_381)))))
      | ~ v3_pre_topc(B_380,g1_pre_topc(u1_struct_0(A_381),u1_pre_topc(A_381)))
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5085,plain,(
    ! [B_380] :
      ( m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_380,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_5063])).

tff(c_5098,plain,(
    ! [B_382] :
      ( m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_382,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_5085])).

tff(c_5127,plain,(
    ! [B_383] :
      ( r1_tarski(B_383,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_383,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_383,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5098,c_12])).

tff(c_5156,plain,
    ( r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_5127])).

tff(c_5174,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4927,c_5156])).

tff(c_5176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4436,c_5174])).

tff(c_5177,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_4434])).

tff(c_5188,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5177,c_82])).

tff(c_8678,plain,(
    ! [C_477,A_478] :
      ( m1_pre_topc(C_477,A_478)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_477),u1_pre_topc(C_477)),A_478)
      | ~ l1_pre_topc(C_477)
      | ~ v2_pre_topc(C_477)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_477),u1_pre_topc(C_477)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_477),u1_pre_topc(C_477)))
      | ~ l1_pre_topc(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8690,plain,(
    ! [A_478] :
      ( m1_pre_topc('#skF_5',A_478)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')),A_478)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_478) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5177,c_8678])).

tff(c_8697,plain,(
    ! [A_479] :
      ( m1_pre_topc('#skF_5',A_479)
      | ~ m1_pre_topc('#skF_6',A_479)
      | ~ l1_pre_topc(A_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5188,c_5177,c_84,c_5188,c_5177,c_90,c_88,c_5188,c_8690])).

tff(c_216,plain,(
    ! [B_82,A_83] :
      ( v3_pre_topc(B_82,A_83)
      | ~ r2_hidden(B_82,u1_pre_topc(A_83))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_247,plain,(
    ! [A_85] :
      ( v3_pre_topc(u1_struct_0(A_85),A_85)
      | ~ r2_hidden(u1_struct_0(A_85),u1_pre_topc(A_85))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_113,c_216])).

tff(c_262,plain,(
    ! [A_7] :
      ( v3_pre_topc(u1_struct_0(A_7),A_7)
      | ~ v2_pre_topc(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_50,c_247])).

tff(c_281,plain,(
    ! [B_89,A_90] :
      ( v3_pre_topc(B_89,g1_pre_topc(u1_struct_0(A_90),u1_pre_topc(A_90)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ v3_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_284,plain,(
    ! [B_89] :
      ( v3_pre_topc(B_89,'#skF_6')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_89,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_281])).

tff(c_287,plain,(
    ! [B_91] :
      ( v3_pre_topc(B_91,'#skF_6')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_91,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_284])).

tff(c_304,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_287])).

tff(c_305,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_308,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_262,c_305])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_90,c_308])).

tff(c_314,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_567,plain,(
    ! [B_122,A_123] :
      ( m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_123),u1_pre_topc(A_123)))))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v3_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_579,plain,(
    ! [B_122] :
      ( m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_122,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_567])).

tff(c_585,plain,(
    ! [B_124] :
      ( m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_124,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_579])).

tff(c_605,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_585])).

tff(c_618,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_605])).

tff(c_634,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_618,c_12])).

tff(c_655,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_634,c_2])).

tff(c_662,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_1052,plain,(
    ! [B_152,A_153] :
      ( v3_pre_topc(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)))))
      | ~ v3_pre_topc(B_152,g1_pre_topc(u1_struct_0(A_153),u1_pre_topc(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1074,plain,(
    ! [B_152] :
      ( v3_pre_topc(B_152,'#skF_5')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_152,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1052])).

tff(c_1087,plain,(
    ! [B_154] :
      ( v3_pre_topc(B_154,'#skF_5')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_154,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_1074])).

tff(c_1132,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_1087])).

tff(c_1133,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1132])).

tff(c_1142,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_262,c_1133])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_1142])).

tff(c_1152,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1132])).

tff(c_1521,plain,(
    ! [B_180,A_181] :
      ( m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_181),u1_pre_topc(A_181)))))
      | ~ v3_pre_topc(B_180,g1_pre_topc(u1_struct_0(A_181),u1_pre_topc(A_181)))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1543,plain,(
    ! [B_180] :
      ( m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_180,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1521])).

tff(c_1556,plain,(
    ! [B_182] :
      ( m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_182,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_1543])).

tff(c_1585,plain,(
    ! [B_183] :
      ( r1_tarski(B_183,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_183,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1556,c_12])).

tff(c_1614,plain,
    ( r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_1585])).

tff(c_1632,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_1614])).

tff(c_1634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_662,c_1632])).

tff(c_1635,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_1645,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_82])).

tff(c_3798,plain,(
    ! [C_268,A_269] :
      ( m1_pre_topc(C_268,A_269)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_268),u1_pre_topc(C_268)),A_269)
      | ~ l1_pre_topc(C_268)
      | ~ v2_pre_topc(C_268)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_268),u1_pre_topc(C_268)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_268),u1_pre_topc(C_268)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3801,plain,(
    ! [A_269] :
      ( m1_pre_topc('#skF_5',A_269)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')),A_269)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_3798])).

tff(c_3808,plain,(
    ! [A_270] :
      ( m1_pre_topc('#skF_5',A_270)
      | ~ m1_pre_topc('#skF_6',A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1645,c_1635,c_84,c_1645,c_1635,c_90,c_88,c_1645,c_3801])).

tff(c_94,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_110,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_132,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_80,plain,(
    ! [B_49,A_47] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_438,plain,(
    ! [B_104,A_105] :
      ( v3_pre_topc(u1_struct_0(B_104),A_105)
      | ~ v1_tsep_1(B_104,A_105)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_449,plain,(
    ! [B_49,A_47] :
      ( v3_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v1_tsep_1(B_49,A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_438])).

tff(c_461,plain,(
    ! [B_109,A_110] :
      ( v1_tsep_1(B_109,A_110)
      | ~ v3_pre_topc(u1_struct_0(B_109),A_110)
      | ~ m1_subset_1(u1_struct_0(B_109),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_pre_topc(B_109,A_110)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_472,plain,(
    ! [B_49,A_47] :
      ( v1_tsep_1(B_49,A_47)
      | ~ v3_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_461])).

tff(c_2515,plain,(
    ! [A_207] :
      ( v1_tsep_1('#skF_5',A_207)
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),A_207)
      | ~ v2_pre_topc(A_207)
      | ~ m1_pre_topc('#skF_5',A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_472])).

tff(c_2823,plain,(
    ! [A_216] :
      ( v1_tsep_1('#skF_5',A_216)
      | ~ m1_pre_topc('#skF_5',A_216)
      | ~ v1_tsep_1('#skF_6',A_216)
      | ~ v2_pre_topc(A_216)
      | ~ m1_pre_topc('#skF_6',A_216)
      | ~ l1_pre_topc(A_216) ) ),
    inference(resolution,[status(thm)],[c_449,c_2515])).

tff(c_96,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_153,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_126,c_96])).

tff(c_154,plain,(
    ~ v1_tsep_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_2833,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2823,c_154])).

tff(c_2840,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126,c_94,c_132,c_2833])).

tff(c_3813,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3808,c_2840])).

tff(c_3848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126,c_3813])).

tff(c_3849,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_8734,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8697,c_3849])).

tff(c_8770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126,c_8734])).

tff(c_8772,plain,(
    ~ v1_tsep_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_8771,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_112,plain,
    ( v1_tsep_1('#skF_5','#skF_4')
    | v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_8773,plain,(
    v1_tsep_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_8772,c_112])).

tff(c_8860,plain,(
    ! [B_500,A_501] :
      ( v3_pre_topc(B_500,A_501)
      | ~ r2_hidden(B_500,u1_pre_topc(A_501))
      | ~ m1_subset_1(B_500,k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ l1_pre_topc(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8875,plain,(
    ! [A_502] :
      ( v3_pre_topc(u1_struct_0(A_502),A_502)
      | ~ r2_hidden(u1_struct_0(A_502),u1_pre_topc(A_502))
      | ~ l1_pre_topc(A_502) ) ),
    inference(resolution,[status(thm)],[c_113,c_8860])).

tff(c_8879,plain,(
    ! [A_7] :
      ( v3_pre_topc(u1_struct_0(A_7),A_7)
      | ~ v2_pre_topc(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_50,c_8875])).

tff(c_8965,plain,(
    ! [B_517,A_518] :
      ( v3_pre_topc(B_517,g1_pre_topc(u1_struct_0(A_518),u1_pre_topc(A_518)))
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ v3_pre_topc(B_517,A_518)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8968,plain,(
    ! [B_517] :
      ( v3_pre_topc(B_517,'#skF_6')
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_517,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8965])).

tff(c_8971,plain,(
    ! [B_519] :
      ( v3_pre_topc(B_519,'#skF_6')
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_519,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_8968])).

tff(c_8988,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_8971])).

tff(c_8989,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8988])).

tff(c_8992,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_8879,c_8989])).

tff(c_8996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_90,c_8992])).

tff(c_8998,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_8988])).

tff(c_9277,plain,(
    ! [B_545,A_546] :
      ( m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_546),u1_pre_topc(A_546)))))
      | ~ m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ v3_pre_topc(B_545,A_546)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9289,plain,(
    ! [B_545] :
      ( m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_545,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_9277])).

tff(c_9304,plain,(
    ! [B_549] :
      ( m1_subset_1(B_549,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_549,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_549,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_9289])).

tff(c_9324,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_9304])).

tff(c_9337,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8998,c_9324])).

tff(c_9370,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9337,c_12])).

tff(c_9391,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_9370,c_2])).

tff(c_9398,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9391])).

tff(c_9790,plain,(
    ! [B_585,A_586] :
      ( v3_pre_topc(B_585,A_586)
      | ~ m1_subset_1(B_585,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_586),u1_pre_topc(A_586)))))
      | ~ v3_pre_topc(B_585,g1_pre_topc(u1_struct_0(A_586),u1_pre_topc(A_586)))
      | ~ l1_pre_topc(A_586)
      | ~ v2_pre_topc(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9812,plain,(
    ! [B_585] :
      ( v3_pre_topc(B_585,'#skF_5')
      | ~ m1_subset_1(B_585,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_585,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_9790])).

tff(c_9825,plain,(
    ! [B_587] :
      ( v3_pre_topc(B_587,'#skF_5')
      | ~ m1_subset_1(B_587,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_587,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_9812])).

tff(c_9870,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_9825])).

tff(c_9871,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9870])).

tff(c_9880,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_8879,c_9871])).

tff(c_9888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_9880])).

tff(c_9890,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_9870])).

tff(c_10232,plain,(
    ! [B_605,A_606] :
      ( m1_subset_1(B_605,k1_zfmisc_1(u1_struct_0(A_606)))
      | ~ m1_subset_1(B_605,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_606),u1_pre_topc(A_606)))))
      | ~ v3_pre_topc(B_605,g1_pre_topc(u1_struct_0(A_606),u1_pre_topc(A_606)))
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10254,plain,(
    ! [B_605] :
      ( m1_subset_1(B_605,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_605,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_605,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10232])).

tff(c_10267,plain,(
    ! [B_607] :
      ( m1_subset_1(B_607,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_607,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_607,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_10254])).

tff(c_10296,plain,(
    ! [B_608] :
      ( r1_tarski(B_608,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_608,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_608,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10267,c_12])).

tff(c_10325,plain,
    ( r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_10296])).

tff(c_10343,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9890,c_10325])).

tff(c_10345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9398,c_10343])).

tff(c_10346,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_9391])).

tff(c_9206,plain,(
    ! [B_536,A_537] :
      ( v3_pre_topc(u1_struct_0(B_536),A_537)
      | ~ v1_tsep_1(B_536,A_537)
      | ~ m1_subset_1(u1_struct_0(B_536),k1_zfmisc_1(u1_struct_0(A_537)))
      | ~ m1_pre_topc(B_536,A_537)
      | ~ l1_pre_topc(A_537)
      | ~ v2_pre_topc(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9217,plain,(
    ! [B_49,A_47] :
      ( v3_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v1_tsep_1(B_49,A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_9206])).

tff(c_11658,plain,(
    ! [A_641] :
      ( v3_pre_topc(u1_struct_0('#skF_6'),A_641)
      | ~ v1_tsep_1('#skF_5',A_641)
      | ~ v2_pre_topc(A_641)
      | ~ m1_pre_topc('#skF_5',A_641)
      | ~ l1_pre_topc(A_641) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10346,c_9217])).

tff(c_9229,plain,(
    ! [B_541,A_542] :
      ( v1_tsep_1(B_541,A_542)
      | ~ v3_pre_topc(u1_struct_0(B_541),A_542)
      | ~ m1_subset_1(u1_struct_0(B_541),k1_zfmisc_1(u1_struct_0(A_542)))
      | ~ m1_pre_topc(B_541,A_542)
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9240,plain,(
    ! [B_49,A_47] :
      ( v1_tsep_1(B_49,A_47)
      | ~ v3_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_9229])).

tff(c_11700,plain,(
    ! [A_644] :
      ( v1_tsep_1('#skF_6',A_644)
      | ~ m1_pre_topc('#skF_6',A_644)
      | ~ v1_tsep_1('#skF_5',A_644)
      | ~ v2_pre_topc(A_644)
      | ~ m1_pre_topc('#skF_5',A_644)
      | ~ l1_pre_topc(A_644) ) ),
    inference(resolution,[status(thm)],[c_11658,c_9240])).

tff(c_11710,plain,
    ( v1_tsep_1('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8773,c_11700])).

tff(c_11717,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_8771,c_94,c_126,c_11710])).

tff(c_11719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8772,c_11717])).

tff(c_11721,plain,(
    ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_104,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_11722,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_11721,c_104])).

tff(c_11772,plain,(
    ! [B_660,A_661] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_660),u1_pre_topc(B_660)),A_661)
      | ~ m1_pre_topc(B_660,A_661)
      | ~ l1_pre_topc(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_11783,plain,(
    ! [A_662] :
      ( m1_pre_topc('#skF_6',A_662)
      | ~ m1_pre_topc('#skF_5',A_662)
      | ~ l1_pre_topc(A_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_11772])).

tff(c_11786,plain,
    ( m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_11722,c_11783])).

tff(c_11789,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_11786])).

tff(c_11791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11721,c_11789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.31  
% 9.27/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.31  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 9.27/3.31  
% 9.27/3.31  %Foreground sorts:
% 9.27/3.31  
% 9.27/3.31  
% 9.27/3.31  %Background operators:
% 9.27/3.31  
% 9.27/3.31  
% 9.27/3.31  %Foreground operators:
% 9.27/3.31  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.27/3.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.27/3.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.27/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.27/3.31  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.27/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.27/3.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.27/3.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.27/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.27/3.31  tff('#skF_5', type, '#skF_5': $i).
% 9.27/3.31  tff('#skF_6', type, '#skF_6': $i).
% 9.27/3.31  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.27/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.27/3.31  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 9.27/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.27/3.31  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 9.27/3.31  tff('#skF_4', type, '#skF_4': $i).
% 9.27/3.31  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.27/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.27/3.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.27/3.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.27/3.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.27/3.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.27/3.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.27/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.27/3.31  
% 9.27/3.34  tff(f_170, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tmap_1)).
% 9.27/3.34  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 9.27/3.34  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 9.27/3.34  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.27/3.34  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 9.27/3.34  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 9.27/3.34  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.27/3.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.27/3.34  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 9.27/3.34  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.27/3.34  tff(f_138, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 9.27/3.34  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 9.27/3.34  tff(c_92, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_106, plain, (v1_tsep_1('#skF_5', '#skF_4') | m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_126, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_106])).
% 9.27/3.34  tff(c_86, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_88, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_90, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_50, plain, (![A_7]: (r2_hidden(u1_struct_0(A_7), u1_pre_topc(A_7)) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.27/3.34  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.27/3.34  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.27/3.34  tff(c_113, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 9.27/3.34  tff(c_3895, plain, (![B_285, A_286]: (v3_pre_topc(B_285, A_286) | ~r2_hidden(B_285, u1_pre_topc(A_286)) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.27/3.34  tff(c_3910, plain, (![A_287]: (v3_pre_topc(u1_struct_0(A_287), A_287) | ~r2_hidden(u1_struct_0(A_287), u1_pre_topc(A_287)) | ~l1_pre_topc(A_287))), inference(resolution, [status(thm)], [c_113, c_3895])).
% 9.27/3.34  tff(c_3914, plain, (![A_7]: (v3_pre_topc(u1_struct_0(A_7), A_7) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_50, c_3910])).
% 9.27/3.34  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_3992, plain, (![B_299, A_300]: (v3_pre_topc(B_299, g1_pre_topc(u1_struct_0(A_300), u1_pre_topc(A_300))) | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0(A_300))) | ~v3_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_3995, plain, (![B_299]: (v3_pre_topc(B_299, '#skF_6') | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_299, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_3992])).
% 9.27/3.34  tff(c_3998, plain, (![B_301]: (v3_pre_topc(B_301, '#skF_6') | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_301, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_3995])).
% 9.27/3.34  tff(c_4015, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_3998])).
% 9.27/3.34  tff(c_4016, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4015])).
% 9.27/3.34  tff(c_4019, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3914, c_4016])).
% 9.27/3.34  tff(c_4023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_4019])).
% 9.27/3.34  tff(c_4025, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_4015])).
% 9.27/3.34  tff(c_4329, plain, (![B_337, A_338]: (m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_338), u1_pre_topc(A_338))))) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(A_338))) | ~v3_pre_topc(B_337, A_338) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_4341, plain, (![B_337]: (m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_337, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4329])).
% 9.27/3.34  tff(c_4347, plain, (![B_339]: (m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_339, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4341])).
% 9.27/3.34  tff(c_4367, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_4347])).
% 9.27/3.34  tff(c_4380, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4025, c_4367])).
% 9.27/3.34  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.27/3.34  tff(c_4396, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_4380, c_12])).
% 9.27/3.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.27/3.34  tff(c_4434, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4396, c_2])).
% 9.27/3.34  tff(c_4436, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_4434])).
% 9.27/3.34  tff(c_84, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_4827, plain, (![B_371, A_372]: (v3_pre_topc(B_371, A_372) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_372), u1_pre_topc(A_372))))) | ~v3_pre_topc(B_371, g1_pre_topc(u1_struct_0(A_372), u1_pre_topc(A_372))) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_4849, plain, (![B_371]: (v3_pre_topc(B_371, '#skF_5') | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_371, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4827])).
% 9.27/3.34  tff(c_4862, plain, (![B_373]: (v3_pre_topc(B_373, '#skF_5') | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_373, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_4849])).
% 9.27/3.34  tff(c_4907, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_4862])).
% 9.27/3.34  tff(c_4908, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_4907])).
% 9.27/3.34  tff(c_4917, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_3914, c_4908])).
% 9.27/3.34  tff(c_4925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_4917])).
% 9.27/3.34  tff(c_4927, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_4907])).
% 9.27/3.34  tff(c_5063, plain, (![B_380, A_381]: (m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_381))) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_381), u1_pre_topc(A_381))))) | ~v3_pre_topc(B_380, g1_pre_topc(u1_struct_0(A_381), u1_pre_topc(A_381))) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_5085, plain, (![B_380]: (m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_380, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_5063])).
% 9.27/3.34  tff(c_5098, plain, (![B_382]: (m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_382, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_5085])).
% 9.27/3.34  tff(c_5127, plain, (![B_383]: (r1_tarski(B_383, u1_struct_0('#skF_5')) | ~m1_subset_1(B_383, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_383, '#skF_6'))), inference(resolution, [status(thm)], [c_5098, c_12])).
% 9.27/3.34  tff(c_5156, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_5127])).
% 9.27/3.34  tff(c_5174, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4927, c_5156])).
% 9.27/3.34  tff(c_5176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4436, c_5174])).
% 9.27/3.34  tff(c_5177, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_4434])).
% 9.27/3.34  tff(c_5188, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5177, c_82])).
% 9.27/3.34  tff(c_8678, plain, (![C_477, A_478]: (m1_pre_topc(C_477, A_478) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_477), u1_pre_topc(C_477)), A_478) | ~l1_pre_topc(C_477) | ~v2_pre_topc(C_477) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_477), u1_pre_topc(C_477))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_477), u1_pre_topc(C_477))) | ~l1_pre_topc(A_478))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.27/3.34  tff(c_8690, plain, (![A_478]: (m1_pre_topc('#skF_5', A_478) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5')), A_478) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_478))), inference(superposition, [status(thm), theory('equality')], [c_5177, c_8678])).
% 9.27/3.34  tff(c_8697, plain, (![A_479]: (m1_pre_topc('#skF_5', A_479) | ~m1_pre_topc('#skF_6', A_479) | ~l1_pre_topc(A_479))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5188, c_5177, c_84, c_5188, c_5177, c_90, c_88, c_5188, c_8690])).
% 9.27/3.34  tff(c_216, plain, (![B_82, A_83]: (v3_pre_topc(B_82, A_83) | ~r2_hidden(B_82, u1_pre_topc(A_83)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.27/3.34  tff(c_247, plain, (![A_85]: (v3_pre_topc(u1_struct_0(A_85), A_85) | ~r2_hidden(u1_struct_0(A_85), u1_pre_topc(A_85)) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_113, c_216])).
% 9.27/3.34  tff(c_262, plain, (![A_7]: (v3_pre_topc(u1_struct_0(A_7), A_7) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_50, c_247])).
% 9.27/3.34  tff(c_281, plain, (![B_89, A_90]: (v3_pre_topc(B_89, g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~v3_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_284, plain, (![B_89]: (v3_pre_topc(B_89, '#skF_6') | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_89, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_281])).
% 9.27/3.34  tff(c_287, plain, (![B_91]: (v3_pre_topc(B_91, '#skF_6') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_91, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_284])).
% 9.27/3.34  tff(c_304, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_287])).
% 9.27/3.34  tff(c_305, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_304])).
% 9.27/3.34  tff(c_308, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_262, c_305])).
% 9.27/3.34  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_308])).
% 9.27/3.34  tff(c_314, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_304])).
% 9.27/3.34  tff(c_567, plain, (![B_122, A_123]: (m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_123), u1_pre_topc(A_123))))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~v3_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_579, plain, (![B_122]: (m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_122, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_567])).
% 9.27/3.34  tff(c_585, plain, (![B_124]: (m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_124, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_579])).
% 9.27/3.34  tff(c_605, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_585])).
% 9.27/3.34  tff(c_618, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_605])).
% 9.27/3.34  tff(c_634, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_618, c_12])).
% 9.27/3.34  tff(c_655, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_634, c_2])).
% 9.27/3.34  tff(c_662, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_655])).
% 9.27/3.34  tff(c_1052, plain, (![B_152, A_153]: (v3_pre_topc(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153))))) | ~v3_pre_topc(B_152, g1_pre_topc(u1_struct_0(A_153), u1_pre_topc(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_1074, plain, (![B_152]: (v3_pre_topc(B_152, '#skF_5') | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_152, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1052])).
% 9.27/3.34  tff(c_1087, plain, (![B_154]: (v3_pre_topc(B_154, '#skF_5') | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_154, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_1074])).
% 9.27/3.34  tff(c_1132, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_1087])).
% 9.27/3.34  tff(c_1133, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1132])).
% 9.27/3.34  tff(c_1142, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_262, c_1133])).
% 9.27/3.34  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_1142])).
% 9.27/3.34  tff(c_1152, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_1132])).
% 9.27/3.34  tff(c_1521, plain, (![B_180, A_181]: (m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_181))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_181), u1_pre_topc(A_181))))) | ~v3_pre_topc(B_180, g1_pre_topc(u1_struct_0(A_181), u1_pre_topc(A_181))) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_1543, plain, (![B_180]: (m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_180, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1521])).
% 9.27/3.34  tff(c_1556, plain, (![B_182]: (m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_182, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_1543])).
% 9.27/3.34  tff(c_1585, plain, (![B_183]: (r1_tarski(B_183, u1_struct_0('#skF_5')) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_183, '#skF_6'))), inference(resolution, [status(thm)], [c_1556, c_12])).
% 9.27/3.34  tff(c_1614, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_1585])).
% 9.27/3.34  tff(c_1632, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_1614])).
% 9.27/3.34  tff(c_1634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_662, c_1632])).
% 9.27/3.34  tff(c_1635, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_655])).
% 9.27/3.34  tff(c_1645, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1635, c_82])).
% 9.27/3.34  tff(c_3798, plain, (![C_268, A_269]: (m1_pre_topc(C_268, A_269) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_268), u1_pre_topc(C_268)), A_269) | ~l1_pre_topc(C_268) | ~v2_pre_topc(C_268) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_268), u1_pre_topc(C_268))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_268), u1_pre_topc(C_268))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.27/3.34  tff(c_3801, plain, (![A_269]: (m1_pre_topc('#skF_5', A_269) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5')), A_269) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_269))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_3798])).
% 9.27/3.34  tff(c_3808, plain, (![A_270]: (m1_pre_topc('#skF_5', A_270) | ~m1_pre_topc('#skF_6', A_270) | ~l1_pre_topc(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1645, c_1635, c_84, c_1645, c_1635, c_90, c_88, c_1645, c_3801])).
% 9.27/3.34  tff(c_94, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_110, plain, (m1_pre_topc('#skF_5', '#skF_4') | v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_132, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_110])).
% 9.27/3.34  tff(c_80, plain, (![B_49, A_47]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.27/3.34  tff(c_438, plain, (![B_104, A_105]: (v3_pre_topc(u1_struct_0(B_104), A_105) | ~v1_tsep_1(B_104, A_105) | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.27/3.34  tff(c_449, plain, (![B_49, A_47]: (v3_pre_topc(u1_struct_0(B_49), A_47) | ~v1_tsep_1(B_49, A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_438])).
% 9.27/3.34  tff(c_461, plain, (![B_109, A_110]: (v1_tsep_1(B_109, A_110) | ~v3_pre_topc(u1_struct_0(B_109), A_110) | ~m1_subset_1(u1_struct_0(B_109), k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_pre_topc(B_109, A_110) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.27/3.34  tff(c_472, plain, (![B_49, A_47]: (v1_tsep_1(B_49, A_47) | ~v3_pre_topc(u1_struct_0(B_49), A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_461])).
% 9.27/3.34  tff(c_2515, plain, (![A_207]: (v1_tsep_1('#skF_5', A_207) | ~v3_pre_topc(u1_struct_0('#skF_6'), A_207) | ~v2_pre_topc(A_207) | ~m1_pre_topc('#skF_5', A_207) | ~l1_pre_topc(A_207))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_472])).
% 9.27/3.34  tff(c_2823, plain, (![A_216]: (v1_tsep_1('#skF_5', A_216) | ~m1_pre_topc('#skF_5', A_216) | ~v1_tsep_1('#skF_6', A_216) | ~v2_pre_topc(A_216) | ~m1_pre_topc('#skF_6', A_216) | ~l1_pre_topc(A_216))), inference(resolution, [status(thm)], [c_449, c_2515])).
% 9.27/3.34  tff(c_96, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~v1_tsep_1('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_153, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_126, c_96])).
% 9.27/3.34  tff(c_154, plain, (~v1_tsep_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_153])).
% 9.27/3.34  tff(c_2833, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2823, c_154])).
% 9.27/3.34  tff(c_2840, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_126, c_94, c_132, c_2833])).
% 9.27/3.34  tff(c_3813, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3808, c_2840])).
% 9.27/3.34  tff(c_3848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_126, c_3813])).
% 9.27/3.34  tff(c_3849, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_153])).
% 9.27/3.34  tff(c_8734, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8697, c_3849])).
% 9.27/3.34  tff(c_8770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_126, c_8734])).
% 9.27/3.34  tff(c_8772, plain, (~v1_tsep_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 9.27/3.34  tff(c_8771, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 9.27/3.34  tff(c_112, plain, (v1_tsep_1('#skF_5', '#skF_4') | v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_8773, plain, (v1_tsep_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_8772, c_112])).
% 9.27/3.34  tff(c_8860, plain, (![B_500, A_501]: (v3_pre_topc(B_500, A_501) | ~r2_hidden(B_500, u1_pre_topc(A_501)) | ~m1_subset_1(B_500, k1_zfmisc_1(u1_struct_0(A_501))) | ~l1_pre_topc(A_501))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.27/3.34  tff(c_8875, plain, (![A_502]: (v3_pre_topc(u1_struct_0(A_502), A_502) | ~r2_hidden(u1_struct_0(A_502), u1_pre_topc(A_502)) | ~l1_pre_topc(A_502))), inference(resolution, [status(thm)], [c_113, c_8860])).
% 9.27/3.34  tff(c_8879, plain, (![A_7]: (v3_pre_topc(u1_struct_0(A_7), A_7) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_50, c_8875])).
% 9.27/3.34  tff(c_8965, plain, (![B_517, A_518]: (v3_pre_topc(B_517, g1_pre_topc(u1_struct_0(A_518), u1_pre_topc(A_518))) | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0(A_518))) | ~v3_pre_topc(B_517, A_518) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_8968, plain, (![B_517]: (v3_pre_topc(B_517, '#skF_6') | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_517, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8965])).
% 9.27/3.34  tff(c_8971, plain, (![B_519]: (v3_pre_topc(B_519, '#skF_6') | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_519, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_8968])).
% 9.27/3.34  tff(c_8988, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_8971])).
% 9.27/3.34  tff(c_8989, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_8988])).
% 9.27/3.34  tff(c_8992, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_8879, c_8989])).
% 9.27/3.34  tff(c_8996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_8992])).
% 9.27/3.34  tff(c_8998, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_8988])).
% 9.27/3.34  tff(c_9277, plain, (![B_545, A_546]: (m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_546), u1_pre_topc(A_546))))) | ~m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0(A_546))) | ~v3_pre_topc(B_545, A_546) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_9289, plain, (![B_545]: (m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_545, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_9277])).
% 9.27/3.34  tff(c_9304, plain, (![B_549]: (m1_subset_1(B_549, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_549, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_549, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_9289])).
% 9.27/3.34  tff(c_9324, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_9304])).
% 9.27/3.34  tff(c_9337, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_8998, c_9324])).
% 9.27/3.34  tff(c_9370, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_9337, c_12])).
% 9.27/3.34  tff(c_9391, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_9370, c_2])).
% 9.27/3.34  tff(c_9398, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_9391])).
% 9.27/3.34  tff(c_9790, plain, (![B_585, A_586]: (v3_pre_topc(B_585, A_586) | ~m1_subset_1(B_585, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_586), u1_pre_topc(A_586))))) | ~v3_pre_topc(B_585, g1_pre_topc(u1_struct_0(A_586), u1_pre_topc(A_586))) | ~l1_pre_topc(A_586) | ~v2_pre_topc(A_586))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_9812, plain, (![B_585]: (v3_pre_topc(B_585, '#skF_5') | ~m1_subset_1(B_585, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_585, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_9790])).
% 9.27/3.34  tff(c_9825, plain, (![B_587]: (v3_pre_topc(B_587, '#skF_5') | ~m1_subset_1(B_587, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_587, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_9812])).
% 9.27/3.34  tff(c_9870, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_9825])).
% 9.27/3.34  tff(c_9871, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_9870])).
% 9.27/3.34  tff(c_9880, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_8879, c_9871])).
% 9.27/3.34  tff(c_9888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_9880])).
% 9.27/3.34  tff(c_9890, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_9870])).
% 9.27/3.34  tff(c_10232, plain, (![B_605, A_606]: (m1_subset_1(B_605, k1_zfmisc_1(u1_struct_0(A_606))) | ~m1_subset_1(B_605, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_606), u1_pre_topc(A_606))))) | ~v3_pre_topc(B_605, g1_pre_topc(u1_struct_0(A_606), u1_pre_topc(A_606))) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.27/3.34  tff(c_10254, plain, (![B_605]: (m1_subset_1(B_605, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_605, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_605, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10232])).
% 9.27/3.34  tff(c_10267, plain, (![B_607]: (m1_subset_1(B_607, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_607, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_607, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_10254])).
% 9.27/3.34  tff(c_10296, plain, (![B_608]: (r1_tarski(B_608, u1_struct_0('#skF_5')) | ~m1_subset_1(B_608, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_608, '#skF_6'))), inference(resolution, [status(thm)], [c_10267, c_12])).
% 9.27/3.34  tff(c_10325, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_10296])).
% 9.27/3.34  tff(c_10343, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9890, c_10325])).
% 9.27/3.34  tff(c_10345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9398, c_10343])).
% 9.27/3.34  tff(c_10346, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_9391])).
% 9.27/3.34  tff(c_9206, plain, (![B_536, A_537]: (v3_pre_topc(u1_struct_0(B_536), A_537) | ~v1_tsep_1(B_536, A_537) | ~m1_subset_1(u1_struct_0(B_536), k1_zfmisc_1(u1_struct_0(A_537))) | ~m1_pre_topc(B_536, A_537) | ~l1_pre_topc(A_537) | ~v2_pre_topc(A_537))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.27/3.34  tff(c_9217, plain, (![B_49, A_47]: (v3_pre_topc(u1_struct_0(B_49), A_47) | ~v1_tsep_1(B_49, A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_9206])).
% 9.27/3.34  tff(c_11658, plain, (![A_641]: (v3_pre_topc(u1_struct_0('#skF_6'), A_641) | ~v1_tsep_1('#skF_5', A_641) | ~v2_pre_topc(A_641) | ~m1_pre_topc('#skF_5', A_641) | ~l1_pre_topc(A_641))), inference(superposition, [status(thm), theory('equality')], [c_10346, c_9217])).
% 9.27/3.34  tff(c_9229, plain, (![B_541, A_542]: (v1_tsep_1(B_541, A_542) | ~v3_pre_topc(u1_struct_0(B_541), A_542) | ~m1_subset_1(u1_struct_0(B_541), k1_zfmisc_1(u1_struct_0(A_542))) | ~m1_pre_topc(B_541, A_542) | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.27/3.34  tff(c_9240, plain, (![B_49, A_47]: (v1_tsep_1(B_49, A_47) | ~v3_pre_topc(u1_struct_0(B_49), A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_9229])).
% 9.27/3.34  tff(c_11700, plain, (![A_644]: (v1_tsep_1('#skF_6', A_644) | ~m1_pre_topc('#skF_6', A_644) | ~v1_tsep_1('#skF_5', A_644) | ~v2_pre_topc(A_644) | ~m1_pre_topc('#skF_5', A_644) | ~l1_pre_topc(A_644))), inference(resolution, [status(thm)], [c_11658, c_9240])).
% 9.27/3.34  tff(c_11710, plain, (v1_tsep_1('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8773, c_11700])).
% 9.27/3.34  tff(c_11717, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_8771, c_94, c_126, c_11710])).
% 9.27/3.34  tff(c_11719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8772, c_11717])).
% 9.27/3.34  tff(c_11721, plain, (~m1_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 9.27/3.34  tff(c_104, plain, (m1_pre_topc('#skF_5', '#skF_4') | m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.27/3.34  tff(c_11722, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_11721, c_104])).
% 9.27/3.34  tff(c_11772, plain, (![B_660, A_661]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_660), u1_pre_topc(B_660)), A_661) | ~m1_pre_topc(B_660, A_661) | ~l1_pre_topc(A_661))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.27/3.34  tff(c_11783, plain, (![A_662]: (m1_pre_topc('#skF_6', A_662) | ~m1_pre_topc('#skF_5', A_662) | ~l1_pre_topc(A_662))), inference(superposition, [status(thm), theory('equality')], [c_82, c_11772])).
% 9.27/3.34  tff(c_11786, plain, (m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_11722, c_11783])).
% 9.27/3.34  tff(c_11789, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_11786])).
% 9.27/3.34  tff(c_11791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11721, c_11789])).
% 9.27/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.27/3.34  
% 9.27/3.34  Inference rules
% 9.27/3.34  ----------------------
% 9.27/3.34  #Ref     : 0
% 9.27/3.34  #Sup     : 2194
% 9.27/3.34  #Fact    : 0
% 9.27/3.34  #Define  : 0
% 9.27/3.34  #Split   : 33
% 9.27/3.34  #Chain   : 0
% 9.27/3.34  #Close   : 0
% 9.27/3.34  
% 9.27/3.34  Ordering : KBO
% 9.27/3.34  
% 9.27/3.34  Simplification rules
% 9.27/3.34  ----------------------
% 9.27/3.34  #Subsume      : 670
% 9.27/3.34  #Demod        : 3105
% 9.27/3.34  #Tautology    : 680
% 9.27/3.34  #SimpNegUnit  : 7
% 9.27/3.34  #BackRed      : 26
% 9.27/3.34  
% 9.27/3.34  #Partial instantiations: 0
% 9.27/3.34  #Strategies tried      : 1
% 9.27/3.34  
% 9.27/3.34  Timing (in seconds)
% 9.27/3.34  ----------------------
% 9.27/3.35  Preprocessing        : 0.35
% 9.27/3.35  Parsing              : 0.18
% 9.27/3.35  CNF conversion       : 0.03
% 9.27/3.35  Main loop            : 2.15
% 9.27/3.35  Inferencing          : 0.69
% 9.27/3.35  Reduction            : 0.69
% 9.27/3.35  Demodulation         : 0.47
% 9.27/3.35  BG Simplification    : 0.07
% 9.27/3.35  Subsumption          : 0.58
% 9.27/3.35  Abstraction          : 0.08
% 9.27/3.35  MUC search           : 0.00
% 9.27/3.35  Cooper               : 0.00
% 9.27/3.35  Total                : 2.56
% 9.27/3.35  Index Insertion      : 0.00
% 9.27/3.35  Index Deletion       : 0.00
% 9.27/3.35  Index Matching       : 0.00
% 9.27/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
