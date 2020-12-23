%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:23 EST 2020

% Result     : Theorem 9.81s
% Output     : CNFRefutation 10.06s
% Verified   : 
% Statistics : Number of formulae       :  206 (1212 expanded)
%              Number of leaves         :   38 ( 435 expanded)
%              Depth                    :   15
%              Number of atoms          :  510 (4363 expanded)
%              Number of equality atoms :   16 ( 442 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

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
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

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

tff(f_138,axiom,(
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

tff(f_120,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

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
    ( v1_borsuk_1('#skF_5','#skF_4')
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

tff(c_4987,plain,(
    ! [B_291,A_292] :
      ( v3_pre_topc(B_291,A_292)
      | ~ r2_hidden(B_291,u1_pre_topc(A_292))
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5002,plain,(
    ! [A_293] :
      ( v3_pre_topc(u1_struct_0(A_293),A_293)
      | ~ r2_hidden(u1_struct_0(A_293),u1_pre_topc(A_293))
      | ~ l1_pre_topc(A_293) ) ),
    inference(resolution,[status(thm)],[c_113,c_4987])).

tff(c_5006,plain,(
    ! [A_7] :
      ( v3_pre_topc(u1_struct_0(A_7),A_7)
      | ~ v2_pre_topc(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_50,c_5002])).

tff(c_82,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5102,plain,(
    ! [B_307,A_308] :
      ( v3_pre_topc(B_307,g1_pre_topc(u1_struct_0(A_308),u1_pre_topc(A_308)))
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ v3_pre_topc(B_307,A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5105,plain,(
    ! [B_307] :
      ( v3_pre_topc(B_307,'#skF_6')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_307,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_5102])).

tff(c_5108,plain,(
    ! [B_309] :
      ( v3_pre_topc(B_309,'#skF_6')
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_309,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5105])).

tff(c_5125,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_5108])).

tff(c_5126,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5125])).

tff(c_5129,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_5006,c_5126])).

tff(c_5133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_90,c_5129])).

tff(c_5135,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5125])).

tff(c_5315,plain,(
    ! [B_331,A_332] :
      ( m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_332),u1_pre_topc(A_332)))))
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ v3_pre_topc(B_331,A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5327,plain,(
    ! [B_331] :
      ( m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_331,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_331,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_5315])).

tff(c_5333,plain,(
    ! [B_333] :
      ( m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_333,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5327])).

tff(c_5353,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_5333])).

tff(c_5366,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5135,c_5353])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5382,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_5366,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5403,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5382,c_2])).

tff(c_5410,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5403])).

tff(c_84,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5801,plain,(
    ! [B_367,A_368] :
      ( v3_pre_topc(B_367,A_368)
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_368),u1_pre_topc(A_368)))))
      | ~ v3_pre_topc(B_367,g1_pre_topc(u1_struct_0(A_368),u1_pre_topc(A_368)))
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5823,plain,(
    ! [B_367] :
      ( v3_pre_topc(B_367,'#skF_5')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_367,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_5801])).

tff(c_5836,plain,(
    ! [B_369] :
      ( v3_pre_topc(B_369,'#skF_5')
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_369,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_5823])).

tff(c_5881,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_5836])).

tff(c_5882,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5881])).

tff(c_5885,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_5006,c_5882])).

tff(c_5889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_5885])).

tff(c_5891,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5881])).

tff(c_6113,plain,(
    ! [B_386,A_387] :
      ( m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_387),u1_pre_topc(A_387)))))
      | ~ v3_pre_topc(B_386,g1_pre_topc(u1_struct_0(A_387),u1_pre_topc(A_387)))
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6135,plain,(
    ! [B_386] :
      ( m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_386,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_6113])).

tff(c_6148,plain,(
    ! [B_388] :
      ( m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_388,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_6135])).

tff(c_6177,plain,(
    ! [B_389] :
      ( r1_tarski(B_389,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_389,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6148,c_12])).

tff(c_6206,plain,
    ( r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_6177])).

tff(c_6224,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5891,c_6206])).

tff(c_6226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5410,c_6224])).

tff(c_6227,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5403])).

tff(c_6237,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6227,c_82])).

tff(c_9469,plain,(
    ! [C_487,A_488] :
      ( m1_pre_topc(C_487,A_488)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_487),u1_pre_topc(C_487)),A_488)
      | ~ l1_pre_topc(C_487)
      | ~ v2_pre_topc(C_487)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_487),u1_pre_topc(C_487)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_487),u1_pre_topc(C_487)))
      | ~ l1_pre_topc(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9481,plain,(
    ! [A_488] :
      ( m1_pre_topc('#skF_5',A_488)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')),A_488)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6227,c_9469])).

tff(c_9488,plain,(
    ! [A_489] :
      ( m1_pre_topc('#skF_5',A_489)
      | ~ m1_pre_topc('#skF_6',A_489)
      | ~ l1_pre_topc(A_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6237,c_6227,c_84,c_6237,c_6227,c_90,c_88,c_6237,c_9481])).

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

tff(c_541,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_121),u1_pre_topc(A_121)))))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v3_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_553,plain,(
    ! [B_120] :
      ( m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_120,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_541])).

tff(c_559,plain,(
    ! [B_122] :
      ( m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_122,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_553])).

tff(c_579,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_559])).

tff(c_592,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_579])).

tff(c_608,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_592,c_12])).

tff(c_646,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_608,c_2])).

tff(c_648,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_1058,plain,(
    ! [B_158,A_159] :
      ( v3_pre_topc(B_158,A_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_159),u1_pre_topc(A_159)))))
      | ~ v3_pre_topc(B_158,g1_pre_topc(u1_struct_0(A_159),u1_pre_topc(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1080,plain,(
    ! [B_158] :
      ( v3_pre_topc(B_158,'#skF_5')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_158,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1058])).

tff(c_1093,plain,(
    ! [B_160] :
      ( v3_pre_topc(B_160,'#skF_5')
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_160,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_1080])).

tff(c_1138,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_1093])).

tff(c_1152,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1138])).

tff(c_1155,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_262,c_1152])).

tff(c_1159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_1155])).

tff(c_1161,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_1261,plain,(
    ! [B_167,A_168] :
      ( m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168)))))
      | ~ v3_pre_topc(B_167,g1_pre_topc(u1_struct_0(A_168),u1_pre_topc(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1283,plain,(
    ! [B_167] :
      ( m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_167,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1261])).

tff(c_1296,plain,(
    ! [B_169] :
      ( m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_169,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_1283])).

tff(c_1325,plain,(
    ! [B_170] :
      ( r1_tarski(B_170,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_170,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1296,c_12])).

tff(c_1354,plain,
    ( r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_1325])).

tff(c_1372,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_1354])).

tff(c_1374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_1372])).

tff(c_1375,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_1386,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1375,c_82])).

tff(c_4872,plain,(
    ! [C_274,A_275] :
      ( m1_pre_topc(C_274,A_275)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_274),u1_pre_topc(C_274)),A_275)
      | ~ l1_pre_topc(C_274)
      | ~ v2_pre_topc(C_274)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_274),u1_pre_topc(C_274)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_274),u1_pre_topc(C_274)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4884,plain,(
    ! [A_275] :
      ( m1_pre_topc('#skF_5',A_275)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_5')),A_275)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_4872])).

tff(c_4891,plain,(
    ! [A_276] :
      ( m1_pre_topc('#skF_5',A_276)
      | ~ m1_pre_topc('#skF_6',A_276)
      | ~ l1_pre_topc(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1386,c_1375,c_84,c_1386,c_1375,c_90,c_88,c_1386,c_4884])).

tff(c_94,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_110,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | v1_borsuk_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_132,plain,(
    v1_borsuk_1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_80,plain,(
    ! [B_49,A_47] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_504,plain,(
    ! [B_112,A_113] :
      ( v4_pre_topc(u1_struct_0(B_112),A_113)
      | ~ v1_borsuk_1(B_112,A_113)
      | ~ m1_subset_1(u1_struct_0(B_112),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_515,plain,(
    ! [B_49,A_47] :
      ( v4_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v1_borsuk_1(B_49,A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_504])).

tff(c_438,plain,(
    ! [B_104,A_105] :
      ( v1_borsuk_1(B_104,A_105)
      | ~ v4_pre_topc(u1_struct_0(B_104),A_105)
      | ~ m1_subset_1(u1_struct_0(B_104),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_449,plain,(
    ! [B_49,A_47] :
      ( v1_borsuk_1(B_49,A_47)
      | ~ v4_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_438])).

tff(c_2433,plain,(
    ! [A_200] :
      ( v1_borsuk_1('#skF_5',A_200)
      | ~ v4_pre_topc(u1_struct_0('#skF_6'),A_200)
      | ~ v2_pre_topc(A_200)
      | ~ m1_pre_topc('#skF_5',A_200)
      | ~ l1_pre_topc(A_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_449])).

tff(c_2583,plain,(
    ! [A_204] :
      ( v1_borsuk_1('#skF_5',A_204)
      | ~ m1_pre_topc('#skF_5',A_204)
      | ~ v1_borsuk_1('#skF_6',A_204)
      | ~ v2_pre_topc(A_204)
      | ~ m1_pre_topc('#skF_6',A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(resolution,[status(thm)],[c_515,c_2433])).

tff(c_96,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_borsuk_1('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_borsuk_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_153,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_borsuk_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_126,c_96])).

tff(c_154,plain,(
    ~ v1_borsuk_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_2586,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_borsuk_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2583,c_154])).

tff(c_2589,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126,c_94,c_132,c_2586])).

tff(c_4906,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4891,c_2589])).

tff(c_4940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126,c_4906])).

tff(c_4941,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_9519,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_9488,c_4941])).

tff(c_9549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_126,c_9519])).

tff(c_9551,plain,(
    ~ v1_borsuk_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_9550,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_112,plain,
    ( v1_borsuk_1('#skF_5','#skF_4')
    | v1_borsuk_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_9552,plain,(
    v1_borsuk_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_9551,c_112])).

tff(c_9639,plain,(
    ! [B_510,A_511] :
      ( v3_pre_topc(B_510,A_511)
      | ~ r2_hidden(B_510,u1_pre_topc(A_511))
      | ~ m1_subset_1(B_510,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ l1_pre_topc(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9654,plain,(
    ! [A_512] :
      ( v3_pre_topc(u1_struct_0(A_512),A_512)
      | ~ r2_hidden(u1_struct_0(A_512),u1_pre_topc(A_512))
      | ~ l1_pre_topc(A_512) ) ),
    inference(resolution,[status(thm)],[c_113,c_9639])).

tff(c_9658,plain,(
    ! [A_7] :
      ( v3_pre_topc(u1_struct_0(A_7),A_7)
      | ~ v2_pre_topc(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_50,c_9654])).

tff(c_9744,plain,(
    ! [B_527,A_528] :
      ( v3_pre_topc(B_527,g1_pre_topc(u1_struct_0(A_528),u1_pre_topc(A_528)))
      | ~ m1_subset_1(B_527,k1_zfmisc_1(u1_struct_0(A_528)))
      | ~ v3_pre_topc(B_527,A_528)
      | ~ l1_pre_topc(A_528)
      | ~ v2_pre_topc(A_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9747,plain,(
    ! [B_527] :
      ( v3_pre_topc(B_527,'#skF_6')
      | ~ m1_subset_1(B_527,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_527,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_9744])).

tff(c_9750,plain,(
    ! [B_529] :
      ( v3_pre_topc(B_529,'#skF_6')
      | ~ m1_subset_1(B_529,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_529,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_9747])).

tff(c_9767,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_9750])).

tff(c_9768,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9767])).

tff(c_9771,plain,
    ( ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_9658,c_9768])).

tff(c_9775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_90,c_9771])).

tff(c_9777,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_9767])).

tff(c_10047,plain,(
    ! [B_560,A_561] :
      ( m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_561),u1_pre_topc(A_561)))))
      | ~ m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0(A_561)))
      | ~ v3_pre_topc(B_560,A_561)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10059,plain,(
    ! [B_560] :
      ( m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_560,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_560,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10047])).

tff(c_10065,plain,(
    ! [B_562] :
      ( m1_subset_1(B_562,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_562,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_562,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_10059])).

tff(c_10085,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_10065])).

tff(c_10098,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9777,c_10085])).

tff(c_10114,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10098,c_12])).

tff(c_10135,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10114,c_2])).

tff(c_10142,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10135])).

tff(c_10476,plain,(
    ! [B_587,A_588] :
      ( v3_pre_topc(B_587,A_588)
      | ~ m1_subset_1(B_587,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_588),u1_pre_topc(A_588)))))
      | ~ v3_pre_topc(B_587,g1_pre_topc(u1_struct_0(A_588),u1_pre_topc(A_588)))
      | ~ l1_pre_topc(A_588)
      | ~ v2_pre_topc(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10498,plain,(
    ! [B_587] :
      ( v3_pre_topc(B_587,'#skF_5')
      | ~ m1_subset_1(B_587,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_587,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10476])).

tff(c_10511,plain,(
    ! [B_589] :
      ( v3_pre_topc(B_589,'#skF_5')
      | ~ m1_subset_1(B_589,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_589,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_10498])).

tff(c_10556,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_10511])).

tff(c_10557,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10556])).

tff(c_10560,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_9658,c_10557])).

tff(c_10564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_10560])).

tff(c_10566,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_10556])).

tff(c_10816,plain,(
    ! [B_606,A_607] :
      ( m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0(A_607)))
      | ~ m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_607),u1_pre_topc(A_607)))))
      | ~ v3_pre_topc(B_606,g1_pre_topc(u1_struct_0(A_607),u1_pre_topc(A_607)))
      | ~ l1_pre_topc(A_607)
      | ~ v2_pre_topc(A_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10838,plain,(
    ! [B_606] :
      ( m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_606,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10816])).

tff(c_10851,plain,(
    ! [B_608] :
      ( m1_subset_1(B_608,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_608,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_608,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_10838])).

tff(c_10880,plain,(
    ! [B_609] :
      ( r1_tarski(B_609,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_609,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc(B_609,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10851,c_12])).

tff(c_10909,plain,
    ( r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_10880])).

tff(c_10927,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10566,c_10909])).

tff(c_10929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10142,c_10927])).

tff(c_10930,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_10135])).

tff(c_9908,plain,(
    ! [B_541,A_542] :
      ( v4_pre_topc(u1_struct_0(B_541),A_542)
      | ~ v1_borsuk_1(B_541,A_542)
      | ~ m1_subset_1(u1_struct_0(B_541),k1_zfmisc_1(u1_struct_0(A_542)))
      | ~ m1_pre_topc(B_541,A_542)
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_9919,plain,(
    ! [B_49,A_47] :
      ( v4_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v1_borsuk_1(B_49,A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_9908])).

tff(c_11833,plain,(
    ! [A_631] :
      ( v4_pre_topc(u1_struct_0('#skF_6'),A_631)
      | ~ v1_borsuk_1('#skF_5',A_631)
      | ~ v2_pre_topc(A_631)
      | ~ m1_pre_topc('#skF_5',A_631)
      | ~ l1_pre_topc(A_631) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10930,c_9919])).

tff(c_9955,plain,(
    ! [B_547,A_548] :
      ( v1_borsuk_1(B_547,A_548)
      | ~ v4_pre_topc(u1_struct_0(B_547),A_548)
      | ~ m1_subset_1(u1_struct_0(B_547),k1_zfmisc_1(u1_struct_0(A_548)))
      | ~ m1_pre_topc(B_547,A_548)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_9966,plain,(
    ! [B_49,A_47] :
      ( v1_borsuk_1(B_49,A_47)
      | ~ v4_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_9955])).

tff(c_12154,plain,(
    ! [A_641] :
      ( v1_borsuk_1('#skF_6',A_641)
      | ~ m1_pre_topc('#skF_6',A_641)
      | ~ v1_borsuk_1('#skF_5',A_641)
      | ~ v2_pre_topc(A_641)
      | ~ m1_pre_topc('#skF_5',A_641)
      | ~ l1_pre_topc(A_641) ) ),
    inference(resolution,[status(thm)],[c_11833,c_9966])).

tff(c_12157,plain,
    ( v1_borsuk_1('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_9552,c_12154])).

tff(c_12160,plain,(
    v1_borsuk_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_9550,c_94,c_126,c_12157])).

tff(c_12162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9551,c_12160])).

tff(c_12164,plain,(
    ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_104,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_12167,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12164,c_104])).

tff(c_12215,plain,(
    ! [B_657,A_658] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_657),u1_pre_topc(B_657)),A_658)
      | ~ m1_pre_topc(B_657,A_658)
      | ~ l1_pre_topc(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12226,plain,(
    ! [A_659] :
      ( m1_pre_topc('#skF_6',A_659)
      | ~ m1_pre_topc('#skF_5',A_659)
      | ~ l1_pre_topc(A_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12215])).

tff(c_12229,plain,
    ( m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12167,c_12226])).

tff(c_12232,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12229])).

tff(c_12234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12164,c_12232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.81/3.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.81/3.37  
% 9.81/3.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.06/3.37  %$ v4_pre_topc > v3_pre_topc > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 10.06/3.37  
% 10.06/3.37  %Foreground sorts:
% 10.06/3.37  
% 10.06/3.37  
% 10.06/3.37  %Background operators:
% 10.06/3.37  
% 10.06/3.37  
% 10.06/3.37  %Foreground operators:
% 10.06/3.37  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.06/3.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.06/3.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.06/3.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.06/3.37  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.06/3.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.06/3.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.06/3.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.06/3.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.06/3.37  tff('#skF_5', type, '#skF_5': $i).
% 10.06/3.37  tff('#skF_6', type, '#skF_6': $i).
% 10.06/3.37  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.06/3.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.06/3.37  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 10.06/3.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.06/3.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.06/3.37  tff('#skF_4', type, '#skF_4': $i).
% 10.06/3.37  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.06/3.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.06/3.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.06/3.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.06/3.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.06/3.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.06/3.37  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.06/3.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.06/3.37  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 10.06/3.37  
% 10.06/3.40  tff(f_170, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> (v1_borsuk_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tmap_1)).
% 10.06/3.40  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 10.06/3.40  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 10.06/3.40  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.06/3.40  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 10.06/3.40  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 10.06/3.40  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.06/3.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.06/3.40  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 10.06/3.40  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.06/3.40  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tsep_1)).
% 10.06/3.40  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 10.06/3.40  tff(c_92, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_106, plain, (v1_borsuk_1('#skF_5', '#skF_4') | m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_126, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_106])).
% 10.06/3.40  tff(c_86, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_88, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_90, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_50, plain, (![A_7]: (r2_hidden(u1_struct_0(A_7), u1_pre_topc(A_7)) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.06/3.40  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.06/3.40  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.06/3.40  tff(c_113, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 10.06/3.40  tff(c_4987, plain, (![B_291, A_292]: (v3_pre_topc(B_291, A_292) | ~r2_hidden(B_291, u1_pre_topc(A_292)) | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.06/3.40  tff(c_5002, plain, (![A_293]: (v3_pre_topc(u1_struct_0(A_293), A_293) | ~r2_hidden(u1_struct_0(A_293), u1_pre_topc(A_293)) | ~l1_pre_topc(A_293))), inference(resolution, [status(thm)], [c_113, c_4987])).
% 10.06/3.40  tff(c_5006, plain, (![A_7]: (v3_pre_topc(u1_struct_0(A_7), A_7) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_50, c_5002])).
% 10.06/3.40  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_5102, plain, (![B_307, A_308]: (v3_pre_topc(B_307, g1_pre_topc(u1_struct_0(A_308), u1_pre_topc(A_308))) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_308))) | ~v3_pre_topc(B_307, A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_5105, plain, (![B_307]: (v3_pre_topc(B_307, '#skF_6') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_307, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_5102])).
% 10.06/3.40  tff(c_5108, plain, (![B_309]: (v3_pre_topc(B_309, '#skF_6') | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_309, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5105])).
% 10.06/3.40  tff(c_5125, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_5108])).
% 10.06/3.40  tff(c_5126, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5125])).
% 10.06/3.40  tff(c_5129, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_5006, c_5126])).
% 10.06/3.40  tff(c_5133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_5129])).
% 10.06/3.40  tff(c_5135, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_5125])).
% 10.06/3.40  tff(c_5315, plain, (![B_331, A_332]: (m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_332), u1_pre_topc(A_332))))) | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0(A_332))) | ~v3_pre_topc(B_331, A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_5327, plain, (![B_331]: (m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_331, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_331, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_5315])).
% 10.06/3.40  tff(c_5333, plain, (![B_333]: (m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_333, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5327])).
% 10.06/3.40  tff(c_5353, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_5333])).
% 10.06/3.40  tff(c_5366, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_5135, c_5353])).
% 10.06/3.40  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.06/3.40  tff(c_5382, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_5366, c_12])).
% 10.06/3.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.06/3.40  tff(c_5403, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5382, c_2])).
% 10.06/3.40  tff(c_5410, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_5403])).
% 10.06/3.40  tff(c_84, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_5801, plain, (![B_367, A_368]: (v3_pre_topc(B_367, A_368) | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_368), u1_pre_topc(A_368))))) | ~v3_pre_topc(B_367, g1_pre_topc(u1_struct_0(A_368), u1_pre_topc(A_368))) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_5823, plain, (![B_367]: (v3_pre_topc(B_367, '#skF_5') | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_367, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_5801])).
% 10.06/3.40  tff(c_5836, plain, (![B_369]: (v3_pre_topc(B_369, '#skF_5') | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_369, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_5823])).
% 10.06/3.40  tff(c_5881, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_5836])).
% 10.06/3.40  tff(c_5882, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5881])).
% 10.06/3.40  tff(c_5885, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_5006, c_5882])).
% 10.06/3.40  tff(c_5889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_5885])).
% 10.06/3.40  tff(c_5891, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_5881])).
% 10.06/3.40  tff(c_6113, plain, (![B_386, A_387]: (m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_387))) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_387), u1_pre_topc(A_387))))) | ~v3_pre_topc(B_386, g1_pre_topc(u1_struct_0(A_387), u1_pre_topc(A_387))) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_6135, plain, (![B_386]: (m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_386, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_6113])).
% 10.06/3.40  tff(c_6148, plain, (![B_388]: (m1_subset_1(B_388, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_388, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_388, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_6135])).
% 10.06/3.40  tff(c_6177, plain, (![B_389]: (r1_tarski(B_389, u1_struct_0('#skF_5')) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_389, '#skF_6'))), inference(resolution, [status(thm)], [c_6148, c_12])).
% 10.06/3.40  tff(c_6206, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_6177])).
% 10.06/3.40  tff(c_6224, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5891, c_6206])).
% 10.06/3.40  tff(c_6226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5410, c_6224])).
% 10.06/3.40  tff(c_6227, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_5403])).
% 10.06/3.40  tff(c_6237, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6227, c_82])).
% 10.06/3.40  tff(c_9469, plain, (![C_487, A_488]: (m1_pre_topc(C_487, A_488) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_487), u1_pre_topc(C_487)), A_488) | ~l1_pre_topc(C_487) | ~v2_pre_topc(C_487) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_487), u1_pre_topc(C_487))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_487), u1_pre_topc(C_487))) | ~l1_pre_topc(A_488))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.06/3.40  tff(c_9481, plain, (![A_488]: (m1_pre_topc('#skF_5', A_488) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5')), A_488) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_488))), inference(superposition, [status(thm), theory('equality')], [c_6227, c_9469])).
% 10.06/3.40  tff(c_9488, plain, (![A_489]: (m1_pre_topc('#skF_5', A_489) | ~m1_pre_topc('#skF_6', A_489) | ~l1_pre_topc(A_489))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6237, c_6227, c_84, c_6237, c_6227, c_90, c_88, c_6237, c_9481])).
% 10.06/3.40  tff(c_216, plain, (![B_82, A_83]: (v3_pre_topc(B_82, A_83) | ~r2_hidden(B_82, u1_pre_topc(A_83)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.06/3.40  tff(c_247, plain, (![A_85]: (v3_pre_topc(u1_struct_0(A_85), A_85) | ~r2_hidden(u1_struct_0(A_85), u1_pre_topc(A_85)) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_113, c_216])).
% 10.06/3.40  tff(c_262, plain, (![A_7]: (v3_pre_topc(u1_struct_0(A_7), A_7) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_50, c_247])).
% 10.06/3.40  tff(c_281, plain, (![B_89, A_90]: (v3_pre_topc(B_89, g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~v3_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_284, plain, (![B_89]: (v3_pre_topc(B_89, '#skF_6') | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_89, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_281])).
% 10.06/3.40  tff(c_287, plain, (![B_91]: (v3_pre_topc(B_91, '#skF_6') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_91, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_284])).
% 10.06/3.40  tff(c_304, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_287])).
% 10.06/3.40  tff(c_305, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_304])).
% 10.06/3.40  tff(c_308, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_262, c_305])).
% 10.06/3.40  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_308])).
% 10.06/3.40  tff(c_314, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_304])).
% 10.06/3.40  tff(c_541, plain, (![B_120, A_121]: (m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_121), u1_pre_topc(A_121))))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~v3_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_553, plain, (![B_120]: (m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_120, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_541])).
% 10.06/3.40  tff(c_559, plain, (![B_122]: (m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_122, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_553])).
% 10.06/3.40  tff(c_579, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_559])).
% 10.06/3.40  tff(c_592, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_579])).
% 10.06/3.40  tff(c_608, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_592, c_12])).
% 10.06/3.40  tff(c_646, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_608, c_2])).
% 10.06/3.40  tff(c_648, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_646])).
% 10.06/3.40  tff(c_1058, plain, (![B_158, A_159]: (v3_pre_topc(B_158, A_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_159), u1_pre_topc(A_159))))) | ~v3_pre_topc(B_158, g1_pre_topc(u1_struct_0(A_159), u1_pre_topc(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_1080, plain, (![B_158]: (v3_pre_topc(B_158, '#skF_5') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_158, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1058])).
% 10.06/3.40  tff(c_1093, plain, (![B_160]: (v3_pre_topc(B_160, '#skF_5') | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_160, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_1080])).
% 10.06/3.40  tff(c_1138, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_1093])).
% 10.06/3.40  tff(c_1152, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1138])).
% 10.06/3.40  tff(c_1155, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_262, c_1152])).
% 10.06/3.40  tff(c_1159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_1155])).
% 10.06/3.40  tff(c_1161, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_1138])).
% 10.06/3.40  tff(c_1261, plain, (![B_167, A_168]: (m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))))) | ~v3_pre_topc(B_167, g1_pre_topc(u1_struct_0(A_168), u1_pre_topc(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_1283, plain, (![B_167]: (m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_167, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1261])).
% 10.06/3.40  tff(c_1296, plain, (![B_169]: (m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_169, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_1283])).
% 10.06/3.40  tff(c_1325, plain, (![B_170]: (r1_tarski(B_170, u1_struct_0('#skF_5')) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_170, '#skF_6'))), inference(resolution, [status(thm)], [c_1296, c_12])).
% 10.06/3.40  tff(c_1354, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_1325])).
% 10.06/3.40  tff(c_1372, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_1354])).
% 10.06/3.40  tff(c_1374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_648, c_1372])).
% 10.06/3.40  tff(c_1375, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_646])).
% 10.06/3.40  tff(c_1386, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1375, c_82])).
% 10.06/3.40  tff(c_4872, plain, (![C_274, A_275]: (m1_pre_topc(C_274, A_275) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_274), u1_pre_topc(C_274)), A_275) | ~l1_pre_topc(C_274) | ~v2_pre_topc(C_274) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_274), u1_pre_topc(C_274))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_274), u1_pre_topc(C_274))) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.06/3.40  tff(c_4884, plain, (![A_275]: (m1_pre_topc('#skF_5', A_275) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_5')), A_275) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_275))), inference(superposition, [status(thm), theory('equality')], [c_1375, c_4872])).
% 10.06/3.40  tff(c_4891, plain, (![A_276]: (m1_pre_topc('#skF_5', A_276) | ~m1_pre_topc('#skF_6', A_276) | ~l1_pre_topc(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1386, c_1375, c_84, c_1386, c_1375, c_90, c_88, c_1386, c_4884])).
% 10.06/3.40  tff(c_94, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_110, plain, (m1_pre_topc('#skF_5', '#skF_4') | v1_borsuk_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_132, plain, (v1_borsuk_1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_110])).
% 10.06/3.40  tff(c_80, plain, (![B_49, A_47]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.06/3.40  tff(c_504, plain, (![B_112, A_113]: (v4_pre_topc(u1_struct_0(B_112), A_113) | ~v1_borsuk_1(B_112, A_113) | ~m1_subset_1(u1_struct_0(B_112), k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.06/3.40  tff(c_515, plain, (![B_49, A_47]: (v4_pre_topc(u1_struct_0(B_49), A_47) | ~v1_borsuk_1(B_49, A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_504])).
% 10.06/3.40  tff(c_438, plain, (![B_104, A_105]: (v1_borsuk_1(B_104, A_105) | ~v4_pre_topc(u1_struct_0(B_104), A_105) | ~m1_subset_1(u1_struct_0(B_104), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.06/3.40  tff(c_449, plain, (![B_49, A_47]: (v1_borsuk_1(B_49, A_47) | ~v4_pre_topc(u1_struct_0(B_49), A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_438])).
% 10.06/3.40  tff(c_2433, plain, (![A_200]: (v1_borsuk_1('#skF_5', A_200) | ~v4_pre_topc(u1_struct_0('#skF_6'), A_200) | ~v2_pre_topc(A_200) | ~m1_pre_topc('#skF_5', A_200) | ~l1_pre_topc(A_200))), inference(superposition, [status(thm), theory('equality')], [c_1375, c_449])).
% 10.06/3.40  tff(c_2583, plain, (![A_204]: (v1_borsuk_1('#skF_5', A_204) | ~m1_pre_topc('#skF_5', A_204) | ~v1_borsuk_1('#skF_6', A_204) | ~v2_pre_topc(A_204) | ~m1_pre_topc('#skF_6', A_204) | ~l1_pre_topc(A_204))), inference(resolution, [status(thm)], [c_515, c_2433])).
% 10.06/3.40  tff(c_96, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~v1_borsuk_1('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v1_borsuk_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_153, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_borsuk_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_126, c_96])).
% 10.06/3.40  tff(c_154, plain, (~v1_borsuk_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_153])).
% 10.06/3.40  tff(c_2586, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_borsuk_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2583, c_154])).
% 10.06/3.40  tff(c_2589, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_126, c_94, c_132, c_2586])).
% 10.06/3.40  tff(c_4906, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4891, c_2589])).
% 10.06/3.40  tff(c_4940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_126, c_4906])).
% 10.06/3.40  tff(c_4941, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_153])).
% 10.06/3.40  tff(c_9519, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_9488, c_4941])).
% 10.06/3.40  tff(c_9549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_126, c_9519])).
% 10.06/3.40  tff(c_9551, plain, (~v1_borsuk_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 10.06/3.40  tff(c_9550, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 10.06/3.40  tff(c_112, plain, (v1_borsuk_1('#skF_5', '#skF_4') | v1_borsuk_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_9552, plain, (v1_borsuk_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_9551, c_112])).
% 10.06/3.40  tff(c_9639, plain, (![B_510, A_511]: (v3_pre_topc(B_510, A_511) | ~r2_hidden(B_510, u1_pre_topc(A_511)) | ~m1_subset_1(B_510, k1_zfmisc_1(u1_struct_0(A_511))) | ~l1_pre_topc(A_511))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.06/3.40  tff(c_9654, plain, (![A_512]: (v3_pre_topc(u1_struct_0(A_512), A_512) | ~r2_hidden(u1_struct_0(A_512), u1_pre_topc(A_512)) | ~l1_pre_topc(A_512))), inference(resolution, [status(thm)], [c_113, c_9639])).
% 10.06/3.40  tff(c_9658, plain, (![A_7]: (v3_pre_topc(u1_struct_0(A_7), A_7) | ~v2_pre_topc(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_50, c_9654])).
% 10.06/3.40  tff(c_9744, plain, (![B_527, A_528]: (v3_pre_topc(B_527, g1_pre_topc(u1_struct_0(A_528), u1_pre_topc(A_528))) | ~m1_subset_1(B_527, k1_zfmisc_1(u1_struct_0(A_528))) | ~v3_pre_topc(B_527, A_528) | ~l1_pre_topc(A_528) | ~v2_pre_topc(A_528))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_9747, plain, (![B_527]: (v3_pre_topc(B_527, '#skF_6') | ~m1_subset_1(B_527, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_527, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_9744])).
% 10.06/3.40  tff(c_9750, plain, (![B_529]: (v3_pre_topc(B_529, '#skF_6') | ~m1_subset_1(B_529, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_529, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_9747])).
% 10.06/3.40  tff(c_9767, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_9750])).
% 10.06/3.40  tff(c_9768, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_9767])).
% 10.06/3.40  tff(c_9771, plain, (~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_9658, c_9768])).
% 10.06/3.40  tff(c_9775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_9771])).
% 10.06/3.40  tff(c_9777, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_9767])).
% 10.06/3.40  tff(c_10047, plain, (![B_560, A_561]: (m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_561), u1_pre_topc(A_561))))) | ~m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0(A_561))) | ~v3_pre_topc(B_560, A_561) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_10059, plain, (![B_560]: (m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_560, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_560, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10047])).
% 10.06/3.40  tff(c_10065, plain, (![B_562]: (m1_subset_1(B_562, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_562, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_562, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_10059])).
% 10.06/3.40  tff(c_10085, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_10065])).
% 10.06/3.40  tff(c_10098, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_9777, c_10085])).
% 10.06/3.40  tff(c_10114, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_10098, c_12])).
% 10.06/3.40  tff(c_10135, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_10114, c_2])).
% 10.06/3.40  tff(c_10142, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_10135])).
% 10.06/3.40  tff(c_10476, plain, (![B_587, A_588]: (v3_pre_topc(B_587, A_588) | ~m1_subset_1(B_587, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_588), u1_pre_topc(A_588))))) | ~v3_pre_topc(B_587, g1_pre_topc(u1_struct_0(A_588), u1_pre_topc(A_588))) | ~l1_pre_topc(A_588) | ~v2_pre_topc(A_588))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_10498, plain, (![B_587]: (v3_pre_topc(B_587, '#skF_5') | ~m1_subset_1(B_587, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_587, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10476])).
% 10.06/3.40  tff(c_10511, plain, (![B_589]: (v3_pre_topc(B_589, '#skF_5') | ~m1_subset_1(B_589, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_589, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_10498])).
% 10.06/3.40  tff(c_10556, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_10511])).
% 10.06/3.40  tff(c_10557, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_10556])).
% 10.06/3.40  tff(c_10560, plain, (~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_9658, c_10557])).
% 10.06/3.40  tff(c_10564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_10560])).
% 10.06/3.40  tff(c_10566, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_10556])).
% 10.06/3.40  tff(c_10816, plain, (![B_606, A_607]: (m1_subset_1(B_606, k1_zfmisc_1(u1_struct_0(A_607))) | ~m1_subset_1(B_606, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_607), u1_pre_topc(A_607))))) | ~v3_pre_topc(B_606, g1_pre_topc(u1_struct_0(A_607), u1_pre_topc(A_607))) | ~l1_pre_topc(A_607) | ~v2_pre_topc(A_607))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.06/3.40  tff(c_10838, plain, (![B_606]: (m1_subset_1(B_606, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_606, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_606, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10816])).
% 10.06/3.40  tff(c_10851, plain, (![B_608]: (m1_subset_1(B_608, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_608, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_608, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_10838])).
% 10.06/3.40  tff(c_10880, plain, (![B_609]: (r1_tarski(B_609, u1_struct_0('#skF_5')) | ~m1_subset_1(B_609, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc(B_609, '#skF_6'))), inference(resolution, [status(thm)], [c_10851, c_12])).
% 10.06/3.40  tff(c_10909, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_10880])).
% 10.06/3.40  tff(c_10927, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10566, c_10909])).
% 10.06/3.40  tff(c_10929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10142, c_10927])).
% 10.06/3.40  tff(c_10930, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_10135])).
% 10.06/3.40  tff(c_9908, plain, (![B_541, A_542]: (v4_pre_topc(u1_struct_0(B_541), A_542) | ~v1_borsuk_1(B_541, A_542) | ~m1_subset_1(u1_struct_0(B_541), k1_zfmisc_1(u1_struct_0(A_542))) | ~m1_pre_topc(B_541, A_542) | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.06/3.40  tff(c_9919, plain, (![B_49, A_47]: (v4_pre_topc(u1_struct_0(B_49), A_47) | ~v1_borsuk_1(B_49, A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_9908])).
% 10.06/3.40  tff(c_11833, plain, (![A_631]: (v4_pre_topc(u1_struct_0('#skF_6'), A_631) | ~v1_borsuk_1('#skF_5', A_631) | ~v2_pre_topc(A_631) | ~m1_pre_topc('#skF_5', A_631) | ~l1_pre_topc(A_631))), inference(superposition, [status(thm), theory('equality')], [c_10930, c_9919])).
% 10.06/3.40  tff(c_9955, plain, (![B_547, A_548]: (v1_borsuk_1(B_547, A_548) | ~v4_pre_topc(u1_struct_0(B_547), A_548) | ~m1_subset_1(u1_struct_0(B_547), k1_zfmisc_1(u1_struct_0(A_548))) | ~m1_pre_topc(B_547, A_548) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.06/3.40  tff(c_9966, plain, (![B_49, A_47]: (v1_borsuk_1(B_49, A_47) | ~v4_pre_topc(u1_struct_0(B_49), A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_80, c_9955])).
% 10.06/3.40  tff(c_12154, plain, (![A_641]: (v1_borsuk_1('#skF_6', A_641) | ~m1_pre_topc('#skF_6', A_641) | ~v1_borsuk_1('#skF_5', A_641) | ~v2_pre_topc(A_641) | ~m1_pre_topc('#skF_5', A_641) | ~l1_pre_topc(A_641))), inference(resolution, [status(thm)], [c_11833, c_9966])).
% 10.06/3.40  tff(c_12157, plain, (v1_borsuk_1('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_9552, c_12154])).
% 10.06/3.40  tff(c_12160, plain, (v1_borsuk_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_9550, c_94, c_126, c_12157])).
% 10.06/3.40  tff(c_12162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9551, c_12160])).
% 10.06/3.40  tff(c_12164, plain, (~m1_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 10.06/3.40  tff(c_104, plain, (m1_pre_topc('#skF_5', '#skF_4') | m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.06/3.40  tff(c_12167, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12164, c_104])).
% 10.06/3.40  tff(c_12215, plain, (![B_657, A_658]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_657), u1_pre_topc(B_657)), A_658) | ~m1_pre_topc(B_657, A_658) | ~l1_pre_topc(A_658))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.06/3.40  tff(c_12226, plain, (![A_659]: (m1_pre_topc('#skF_6', A_659) | ~m1_pre_topc('#skF_5', A_659) | ~l1_pre_topc(A_659))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12215])).
% 10.06/3.40  tff(c_12229, plain, (m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12167, c_12226])).
% 10.06/3.40  tff(c_12232, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_12229])).
% 10.06/3.40  tff(c_12234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12164, c_12232])).
% 10.06/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.06/3.40  
% 10.06/3.40  Inference rules
% 10.06/3.40  ----------------------
% 10.06/3.40  #Ref     : 0
% 10.06/3.40  #Sup     : 2428
% 10.06/3.40  #Fact    : 0
% 10.06/3.40  #Define  : 0
% 10.06/3.40  #Split   : 22
% 10.06/3.40  #Chain   : 0
% 10.06/3.40  #Close   : 0
% 10.06/3.40  
% 10.06/3.40  Ordering : KBO
% 10.06/3.40  
% 10.06/3.40  Simplification rules
% 10.06/3.40  ----------------------
% 10.06/3.40  #Subsume      : 432
% 10.06/3.40  #Demod        : 3071
% 10.06/3.40  #Tautology    : 914
% 10.06/3.40  #SimpNegUnit  : 7
% 10.06/3.40  #BackRed      : 25
% 10.06/3.40  
% 10.06/3.40  #Partial instantiations: 0
% 10.06/3.40  #Strategies tried      : 1
% 10.06/3.40  
% 10.06/3.40  Timing (in seconds)
% 10.06/3.40  ----------------------
% 10.06/3.40  Preprocessing        : 0.35
% 10.06/3.40  Parsing              : 0.18
% 10.06/3.40  CNF conversion       : 0.03
% 10.06/3.40  Main loop            : 2.26
% 10.06/3.40  Inferencing          : 0.68
% 10.06/3.40  Reduction            : 0.72
% 10.06/3.40  Demodulation         : 0.51
% 10.06/3.40  BG Simplification    : 0.08
% 10.06/3.40  Subsumption          : 0.65
% 10.06/3.40  Abstraction          : 0.08
% 10.06/3.40  MUC search           : 0.00
% 10.06/3.40  Cooper               : 0.00
% 10.06/3.40  Total                : 2.67
% 10.06/3.40  Index Insertion      : 0.00
% 10.06/3.40  Index Deletion       : 0.00
% 10.06/3.40  Index Matching       : 0.00
% 10.06/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
