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
% DateTime   : Thu Dec  3 10:27:52 EST 2020

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 616 expanded)
%              Number of leaves         :   38 ( 233 expanded)
%              Depth                    :   13
%              Number of atoms          :  368 (1963 expanded)
%              Number of equality atoms :   39 ( 295 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_159,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
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
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_3234,plain,(
    ! [A_293,B_294] :
      ( u1_pre_topc(k6_tmap_1(A_293,B_294)) = k5_tmap_1(A_293,B_294)
      | ~ m1_subset_1(B_294,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3243,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3234])).

tff(c_3252,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3243])).

tff(c_3253,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3252])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_91,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_112,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58])).

tff(c_164,plain,(
    ! [B_63,A_64] :
      ( v3_pre_topc(B_63,A_64)
      | ~ r2_hidden(B_63,u1_pre_topc(A_64))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_164])).

tff(c_177,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_170])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_177])).

tff(c_182,plain,
    ( v1_xboole_0(u1_pre_topc('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_178])).

tff(c_183,plain,(
    ~ m1_subset_1('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_269,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(B_92,k5_tmap_1(A_93,B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_273,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_269])).

tff(c_279,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_273])).

tff(c_280,plain,(
    r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_279])).

tff(c_435,plain,(
    ! [A_107,B_108] :
      ( u1_pre_topc(k6_tmap_1(A_107,B_108)) = k5_tmap_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_444,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_435])).

tff(c_453,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_444])).

tff(c_454,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_453])).

tff(c_210,plain,(
    ! [A_74,B_75] :
      ( l1_pre_topc(k6_tmap_1(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_216,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_210])).

tff(c_223,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_216])).

tff(c_224,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_223])).

tff(c_358,plain,(
    ! [A_104,B_105] :
      ( u1_struct_0(k6_tmap_1(A_104,B_105)) = u1_struct_0(A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_364,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_358])).

tff(c_371,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_364])).

tff(c_372,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_371])).

tff(c_12,plain,(
    ! [A_12] :
      ( m1_subset_1(u1_pre_topc(A_12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_399,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_12])).

tff(c_419,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_399])).

tff(c_456,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_419])).

tff(c_24,plain,(
    ! [A_17] : u1_struct_0(k2_yellow_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [B_20,A_18] :
      ( m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_18)))))
      | ~ v1_tops_2(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_643,plain,(
    ! [B_114,A_115] :
      ( m1_subset_1(B_114,k1_zfmisc_1(u1_pre_topc(A_115)))
      | ~ v1_tops_2(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115))))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_646,plain,
    ( m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_pre_topc('#skF_1')))
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_456,c_643])).

tff(c_662,plain,
    ( m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_pre_topc('#skF_1')))
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_646])).

tff(c_727,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_14,plain,(
    ! [A_13] :
      ( v1_tops_2(u1_pre_topc(A_13),A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_494,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_14])).

tff(c_522,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_494])).

tff(c_1515,plain,(
    ! [B_164,A_165] :
      ( v1_tops_2(B_164,A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_165),u1_pre_topc(A_165))))))
      | ~ v1_tops_2(B_164,g1_pre_topc(u1_struct_0(A_165),u1_pre_topc(A_165)))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1535,plain,(
    ! [B_164] :
      ( v1_tops_2(B_164,'#skF_1')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
      | ~ v1_tops_2(B_164,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_1515])).

tff(c_1547,plain,(
    ! [B_164] :
      ( v1_tops_2(B_164,'#skF_1')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_164,k6_tmap_1('#skF_1','#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_91,c_372,c_1535])).

tff(c_1550,plain,(
    ! [B_166] :
      ( v1_tops_2(B_166,'#skF_1')
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_166,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1547])).

tff(c_1553,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_456,c_1550])).

tff(c_1564,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_1553])).

tff(c_1566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_727,c_1564])).

tff(c_1567,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1577,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,u1_pre_topc('#skF_1'))
      | ~ r2_hidden(A_167,k5_tmap_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1567,c_4])).

tff(c_1584,plain,(
    m1_subset_1('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_280,c_1577])).

tff(c_1596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_1584])).

tff(c_1597,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_2019,plain,(
    ! [A_222,B_223] :
      ( u1_pre_topc(k6_tmap_1(A_222,B_223)) = k5_tmap_1(A_222,B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2028,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2019])).

tff(c_2037,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2028])).

tff(c_2038,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2037])).

tff(c_1620,plain,(
    ! [A_172,B_173] :
      ( l1_pre_topc(k6_tmap_1(A_172,B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1626,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1620])).

tff(c_1633,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1626])).

tff(c_1634,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1633])).

tff(c_1714,plain,(
    ! [A_195,B_196] :
      ( u1_struct_0(k6_tmap_1(A_195,B_196)) = u1_struct_0(A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1720,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1714])).

tff(c_1727,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1720])).

tff(c_1728,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1727])).

tff(c_1755,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_12])).

tff(c_1775,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1755])).

tff(c_28,plain,(
    ! [B_20,A_18] :
      ( v1_tops_2(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_18)))))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1798,plain,(
    ! [B_200,A_201] :
      ( v1_tops_2(B_200,A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_pre_topc(A_201)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_201))))
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_1801,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1775,c_1798])).

tff(c_1817,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1801])).

tff(c_1822,plain,(
    ~ m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1817])).

tff(c_1883,plain,(
    ! [B_210,A_211] :
      ( m1_subset_1(B_210,k1_zfmisc_1(u1_pre_topc(A_211)))
      | ~ v1_tops_2(B_210,A_211)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211))))
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_1886,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_pre_topc('#skF_1')))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1775,c_1883])).

tff(c_1902,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_pre_topc('#skF_1')))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1886])).

tff(c_1903,plain,(
    ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1822,c_1902])).

tff(c_2040,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2038,c_1903])).

tff(c_2094,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_14])).

tff(c_2132,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_2094])).

tff(c_2091,plain,
    ( m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_12])).

tff(c_2130,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1728,c_2091])).

tff(c_3051,plain,(
    ! [B_272,A_273] :
      ( v1_tops_2(B_272,A_273)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_273),u1_pre_topc(A_273))))))
      | ~ v1_tops_2(B_272,g1_pre_topc(u1_struct_0(A_273),u1_pre_topc(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3071,plain,(
    ! [B_272] :
      ( v1_tops_2(B_272,'#skF_1')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
      | ~ v1_tops_2(B_272,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_3051])).

tff(c_3083,plain,(
    ! [B_272] :
      ( v1_tops_2(B_272,'#skF_1')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_272,k6_tmap_1('#skF_1','#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_91,c_1728,c_3071])).

tff(c_3086,plain,(
    ! [B_274] :
      ( v1_tops_2(B_274,'#skF_1')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_274,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3083])).

tff(c_3089,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2130,c_3086])).

tff(c_3100,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2132,c_3089])).

tff(c_3102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2040,c_3100])).

tff(c_3104,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_6,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3108,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_pre_topc('#skF_1'))
      | ~ r2_hidden(A_6,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_3104,c_6])).

tff(c_3112,plain,(
    ! [A_6] : ~ r2_hidden(A_6,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1597,c_3108])).

tff(c_3255,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k5_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3253,c_3112])).

tff(c_1680,plain,(
    ! [B_187,A_188] :
      ( r2_hidden(B_187,k5_tmap_1(A_188,B_187))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1684,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1680])).

tff(c_1690,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1684])).

tff(c_1691,plain,(
    r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1690])).

tff(c_3341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3255,c_1691])).

tff(c_3343,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3342,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3418,plain,(
    ! [B_316,A_317] :
      ( r2_hidden(B_316,u1_pre_topc(A_317))
      | ~ v3_pre_topc(B_316,A_317)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3424,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3418])).

tff(c_3431,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3342,c_3424])).

tff(c_5137,plain,(
    ! [A_416,B_417] :
      ( k5_tmap_1(A_416,B_417) = u1_pre_topc(A_416)
      | ~ r2_hidden(B_417,u1_pre_topc(A_416))
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0(A_416)))
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5146,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_5137])).

tff(c_5155,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3431,c_5146])).

tff(c_5156,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5155])).

tff(c_5427,plain,(
    ! [A_424,B_425] :
      ( g1_pre_topc(u1_struct_0(A_424),k5_tmap_1(A_424,B_425)) = k6_tmap_1(A_424,B_425)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5435,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_5427])).

tff(c_5447,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5156,c_5435])).

tff(c_5449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3343,c_5447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.14  
% 6.16/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.14  %$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1
% 6.22/2.14  
% 6.22/2.14  %Foreground sorts:
% 6.22/2.14  
% 6.22/2.14  
% 6.22/2.14  %Background operators:
% 6.22/2.14  
% 6.22/2.14  
% 6.22/2.14  %Foreground operators:
% 6.22/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.22/2.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.22/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.22/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.22/2.14  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.22/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.22/2.14  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 6.22/2.14  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 6.22/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.22/2.14  tff('#skF_2', type, '#skF_2': $i).
% 6.22/2.14  tff('#skF_1', type, '#skF_1': $i).
% 6.22/2.14  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.22/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.22/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.22/2.14  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 6.22/2.14  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 6.22/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.22/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.22/2.14  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 6.22/2.14  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 6.22/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.22/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.22/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.22/2.14  
% 6.22/2.19  tff(f_174, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 6.22/2.19  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 6.22/2.19  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.22/2.19  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 6.22/2.19  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 6.22/2.19  tff(f_119, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 6.22/2.19  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 6.22/2.19  tff(f_81, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 6.22/2.19  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_1)).
% 6.22/2.19  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => v1_tops_2(u1_pre_topc(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_compts_1)).
% 6.22/2.19  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_compts_1)).
% 6.22/2.19  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.22/2.19  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.22/2.19  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 6.22/2.19  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 6.22/2.19  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.22/2.19  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.22/2.19  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.22/2.19  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.22/2.19  tff(c_3234, plain, (![A_293, B_294]: (u1_pre_topc(k6_tmap_1(A_293, B_294))=k5_tmap_1(A_293, B_294) | ~m1_subset_1(B_294, k1_zfmisc_1(u1_struct_0(A_293))) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.22/2.19  tff(c_3243, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3234])).
% 6.22/2.19  tff(c_3252, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3243])).
% 6.22/2.19  tff(c_3253, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_3252])).
% 6.22/2.19  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.22/2.19  tff(c_64, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.22/2.19  tff(c_91, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 6.22/2.19  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 6.22/2.19  tff(c_112, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58])).
% 6.22/2.19  tff(c_164, plain, (![B_63, A_64]: (v3_pre_topc(B_63, A_64) | ~r2_hidden(B_63, u1_pre_topc(A_64)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.22/2.19  tff(c_170, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_164])).
% 6.22/2.19  tff(c_177, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_170])).
% 6.22/2.19  tff(c_178, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_112, c_177])).
% 6.22/2.19  tff(c_182, plain, (v1_xboole_0(u1_pre_topc('#skF_1')) | ~m1_subset_1('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_178])).
% 6.22/2.19  tff(c_183, plain, (~m1_subset_1('#skF_2', u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_182])).
% 6.22/2.19  tff(c_269, plain, (![B_92, A_93]: (r2_hidden(B_92, k5_tmap_1(A_93, B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.22/2.19  tff(c_273, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_269])).
% 6.22/2.19  tff(c_279, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_273])).
% 6.22/2.19  tff(c_280, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_279])).
% 6.22/2.19  tff(c_435, plain, (![A_107, B_108]: (u1_pre_topc(k6_tmap_1(A_107, B_108))=k5_tmap_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.22/2.19  tff(c_444, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_435])).
% 6.22/2.19  tff(c_453, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_444])).
% 6.22/2.19  tff(c_454, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_453])).
% 6.22/2.19  tff(c_210, plain, (![A_74, B_75]: (l1_pre_topc(k6_tmap_1(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.22/2.19  tff(c_216, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_210])).
% 6.22/2.19  tff(c_223, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_216])).
% 6.22/2.19  tff(c_224, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_223])).
% 6.22/2.19  tff(c_358, plain, (![A_104, B_105]: (u1_struct_0(k6_tmap_1(A_104, B_105))=u1_struct_0(A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.22/2.19  tff(c_364, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_358])).
% 6.22/2.19  tff(c_371, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_364])).
% 6.22/2.19  tff(c_372, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_371])).
% 6.22/2.19  tff(c_12, plain, (![A_12]: (m1_subset_1(u1_pre_topc(A_12), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.22/2.19  tff(c_399, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_372, c_12])).
% 6.22/2.19  tff(c_419, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_399])).
% 6.22/2.19  tff(c_456, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_419])).
% 6.22/2.19  tff(c_24, plain, (![A_17]: (u1_struct_0(k2_yellow_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.22/2.19  tff(c_30, plain, (![B_20, A_18]: (m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_18))))) | ~v1_tops_2(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.22/2.19  tff(c_643, plain, (![B_114, A_115]: (m1_subset_1(B_114, k1_zfmisc_1(u1_pre_topc(A_115))) | ~v1_tops_2(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115)))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 6.22/2.19  tff(c_646, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_pre_topc('#skF_1'))) | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_456, c_643])).
% 6.22/2.19  tff(c_662, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_pre_topc('#skF_1'))) | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_646])).
% 6.22/2.19  tff(c_727, plain, (~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_662])).
% 6.22/2.19  tff(c_14, plain, (![A_13]: (v1_tops_2(u1_pre_topc(A_13), A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.22/2.19  tff(c_494, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_454, c_14])).
% 6.22/2.19  tff(c_522, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_494])).
% 6.22/2.19  tff(c_1515, plain, (![B_164, A_165]: (v1_tops_2(B_164, A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_165), u1_pre_topc(A_165)))))) | ~v1_tops_2(B_164, g1_pre_topc(u1_struct_0(A_165), u1_pre_topc(A_165))) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.22/2.19  tff(c_1535, plain, (![B_164]: (v1_tops_2(B_164, '#skF_1') | ~m1_subset_1(B_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~v1_tops_2(B_164, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_1515])).
% 6.22/2.19  tff(c_1547, plain, (![B_164]: (v1_tops_2(B_164, '#skF_1') | ~m1_subset_1(B_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_164, k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_91, c_372, c_1535])).
% 6.22/2.19  tff(c_1550, plain, (![B_166]: (v1_tops_2(B_166, '#skF_1') | ~m1_subset_1(B_166, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_166, k6_tmap_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1547])).
% 6.22/2.19  tff(c_1553, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_456, c_1550])).
% 6.22/2.19  tff(c_1564, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_1553])).
% 6.22/2.19  tff(c_1566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_727, c_1564])).
% 6.22/2.19  tff(c_1567, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_662])).
% 6.22/2.19  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.22/2.19  tff(c_1577, plain, (![A_167]: (m1_subset_1(A_167, u1_pre_topc('#skF_1')) | ~r2_hidden(A_167, k5_tmap_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1567, c_4])).
% 6.22/2.19  tff(c_1584, plain, (m1_subset_1('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_280, c_1577])).
% 6.22/2.19  tff(c_1596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_1584])).
% 6.22/2.19  tff(c_1597, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_182])).
% 6.22/2.19  tff(c_2019, plain, (![A_222, B_223]: (u1_pre_topc(k6_tmap_1(A_222, B_223))=k5_tmap_1(A_222, B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.22/2.19  tff(c_2028, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2019])).
% 6.22/2.19  tff(c_2037, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2028])).
% 6.22/2.19  tff(c_2038, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_2037])).
% 6.22/2.19  tff(c_1620, plain, (![A_172, B_173]: (l1_pre_topc(k6_tmap_1(A_172, B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.22/2.19  tff(c_1626, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1620])).
% 6.22/2.19  tff(c_1633, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1626])).
% 6.22/2.19  tff(c_1634, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_1633])).
% 6.22/2.19  tff(c_1714, plain, (![A_195, B_196]: (u1_struct_0(k6_tmap_1(A_195, B_196))=u1_struct_0(A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.22/2.19  tff(c_1720, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1714])).
% 6.22/2.19  tff(c_1727, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1720])).
% 6.22/2.19  tff(c_1728, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_1727])).
% 6.22/2.19  tff(c_1755, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_12])).
% 6.22/2.19  tff(c_1775, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1755])).
% 6.22/2.19  tff(c_28, plain, (![B_20, A_18]: (v1_tops_2(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_18))))) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.22/2.19  tff(c_1798, plain, (![B_200, A_201]: (v1_tops_2(B_200, A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_pre_topc(A_201))) | ~m1_subset_1(B_200, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_201)))) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 6.22/2.19  tff(c_1801, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1775, c_1798])).
% 6.22/2.19  tff(c_1817, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1801])).
% 6.22/2.19  tff(c_1822, plain, (~m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1817])).
% 6.22/2.19  tff(c_1883, plain, (![B_210, A_211]: (m1_subset_1(B_210, k1_zfmisc_1(u1_pre_topc(A_211))) | ~v1_tops_2(B_210, A_211) | ~m1_subset_1(B_210, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211)))) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 6.22/2.19  tff(c_1886, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_pre_topc('#skF_1'))) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1775, c_1883])).
% 6.22/2.19  tff(c_1902, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_pre_topc('#skF_1'))) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1886])).
% 6.22/2.19  tff(c_1903, plain, (~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1822, c_1902])).
% 6.22/2.19  tff(c_2040, plain, (~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2038, c_1903])).
% 6.22/2.19  tff(c_2094, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2038, c_14])).
% 6.22/2.19  tff(c_2132, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_2094])).
% 6.22/2.19  tff(c_2091, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2038, c_12])).
% 6.22/2.19  tff(c_2130, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1728, c_2091])).
% 6.22/2.19  tff(c_3051, plain, (![B_272, A_273]: (v1_tops_2(B_272, A_273) | ~m1_subset_1(B_272, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_273), u1_pre_topc(A_273)))))) | ~v1_tops_2(B_272, g1_pre_topc(u1_struct_0(A_273), u1_pre_topc(A_273))) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.22/2.19  tff(c_3071, plain, (![B_272]: (v1_tops_2(B_272, '#skF_1') | ~m1_subset_1(B_272, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~v1_tops_2(B_272, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_3051])).
% 6.22/2.19  tff(c_3083, plain, (![B_272]: (v1_tops_2(B_272, '#skF_1') | ~m1_subset_1(B_272, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_272, k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_91, c_1728, c_3071])).
% 6.22/2.19  tff(c_3086, plain, (![B_274]: (v1_tops_2(B_274, '#skF_1') | ~m1_subset_1(B_274, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_274, k6_tmap_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_3083])).
% 6.22/2.19  tff(c_3089, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2130, c_3086])).
% 6.22/2.19  tff(c_3100, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2132, c_3089])).
% 6.22/2.19  tff(c_3102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2040, c_3100])).
% 6.22/2.19  tff(c_3104, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1817])).
% 6.22/2.19  tff(c_6, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.22/2.19  tff(c_3108, plain, (![A_6]: (~v1_xboole_0(u1_pre_topc('#skF_1')) | ~r2_hidden(A_6, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_3104, c_6])).
% 6.22/2.19  tff(c_3112, plain, (![A_6]: (~r2_hidden(A_6, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1597, c_3108])).
% 6.22/2.19  tff(c_3255, plain, (![A_6]: (~r2_hidden(A_6, k5_tmap_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3253, c_3112])).
% 6.22/2.19  tff(c_1680, plain, (![B_187, A_188]: (r2_hidden(B_187, k5_tmap_1(A_188, B_187)) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.22/2.19  tff(c_1684, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1680])).
% 6.22/2.19  tff(c_1690, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1684])).
% 6.22/2.19  tff(c_1691, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_1690])).
% 6.22/2.19  tff(c_3341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3255, c_1691])).
% 6.22/2.19  tff(c_3343, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 6.22/2.19  tff(c_3342, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 6.22/2.19  tff(c_3418, plain, (![B_316, A_317]: (r2_hidden(B_316, u1_pre_topc(A_317)) | ~v3_pre_topc(B_316, A_317) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.22/2.19  tff(c_3424, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3418])).
% 6.22/2.19  tff(c_3431, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3342, c_3424])).
% 6.22/2.19  tff(c_5137, plain, (![A_416, B_417]: (k5_tmap_1(A_416, B_417)=u1_pre_topc(A_416) | ~r2_hidden(B_417, u1_pre_topc(A_416)) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0(A_416))) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.22/2.19  tff(c_5146, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_5137])).
% 6.22/2.19  tff(c_5155, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3431, c_5146])).
% 6.22/2.19  tff(c_5156, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_5155])).
% 6.22/2.19  tff(c_5427, plain, (![A_424, B_425]: (g1_pre_topc(u1_struct_0(A_424), k5_tmap_1(A_424, B_425))=k6_tmap_1(A_424, B_425) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_424))) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.22/2.19  tff(c_5435, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_5427])).
% 6.22/2.19  tff(c_5447, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5156, c_5435])).
% 6.22/2.19  tff(c_5449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_3343, c_5447])).
% 6.22/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.19  
% 6.22/2.19  Inference rules
% 6.22/2.19  ----------------------
% 6.22/2.19  #Ref     : 0
% 6.22/2.19  #Sup     : 1038
% 6.22/2.19  #Fact    : 0
% 6.22/2.19  #Define  : 0
% 6.22/2.19  #Split   : 42
% 6.22/2.19  #Chain   : 0
% 6.22/2.19  #Close   : 0
% 6.22/2.19  
% 6.22/2.19  Ordering : KBO
% 6.22/2.19  
% 6.22/2.19  Simplification rules
% 6.22/2.19  ----------------------
% 6.22/2.19  #Subsume      : 225
% 6.22/2.19  #Demod        : 1389
% 6.22/2.19  #Tautology    : 284
% 6.22/2.19  #SimpNegUnit  : 203
% 6.22/2.19  #BackRed      : 84
% 6.22/2.19  
% 6.22/2.19  #Partial instantiations: 0
% 6.22/2.19  #Strategies tried      : 1
% 6.22/2.19  
% 6.22/2.19  Timing (in seconds)
% 6.22/2.19  ----------------------
% 6.22/2.19  Preprocessing        : 0.36
% 6.22/2.19  Parsing              : 0.20
% 6.22/2.19  CNF conversion       : 0.02
% 6.22/2.19  Main loop            : 1.05
% 6.22/2.19  Inferencing          : 0.36
% 6.22/2.19  Reduction            : 0.38
% 6.22/2.19  Demodulation         : 0.26
% 6.22/2.19  BG Simplification    : 0.04
% 6.22/2.19  Subsumption          : 0.19
% 6.22/2.19  Abstraction          : 0.05
% 6.22/2.19  MUC search           : 0.00
% 6.22/2.19  Cooper               : 0.00
% 6.22/2.19  Total                : 1.50
% 6.22/2.19  Index Insertion      : 0.00
% 6.22/2.19  Index Deletion       : 0.00
% 6.22/2.19  Index Matching       : 0.00
% 6.22/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
