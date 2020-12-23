%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 215 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  281 ( 695 expanded)
%              Number of equality atoms :   36 ( 103 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(u1_pre_topc(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_74,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_52])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_75,plain,(
    ! [B_32,A_33] :
      ( v3_pre_topc(B_32,A_33)
      | ~ r2_hidden(B_32,u1_pre_topc(A_33))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_81,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_78])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_81])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_282,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,u1_pre_topc(A_65))
      | k5_tmap_1(A_65,B_64) != u1_pre_topc(A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_288,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_282])).

tff(c_293,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_288])).

tff(c_294,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_82,c_293])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k5_tmap_1(A_55,B_56),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_174,plain,(
    ! [A_50,B_51] :
      ( u1_pre_topc(k6_tmap_1(A_50,B_51)) = k5_tmap_1(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_180,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_185,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_180])).

tff(c_186,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_185])).

tff(c_92,plain,(
    ! [A_38,B_39] :
      ( l1_pre_topc(k6_tmap_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_95,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_92])).

tff(c_98,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_95])).

tff(c_99,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_98])).

tff(c_121,plain,(
    ! [A_48,B_49] :
      ( u1_struct_0(k6_tmap_1(A_48,B_49)) = u1_struct_0(A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_124,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_121])).

tff(c_127,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_124])).

tff(c_128,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_127])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( v1_tops_2(B_8,A_6)
      | ~ r1_tarski(B_8,u1_pre_topc(A_6))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_147,plain,(
    ! [B_8] :
      ( v1_tops_2(B_8,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_8,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_12])).

tff(c_167,plain,(
    ! [B_8] :
      ( v1_tops_2(B_8,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_8,u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_147])).

tff(c_213,plain,(
    ! [B_8] :
      ( v1_tops_2(B_8,k6_tmap_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_8,k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_167])).

tff(c_219,plain,(
    ! [B_56] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_56),k6_tmap_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k5_tmap_1('#skF_1',B_56),k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_215,c_213])).

tff(c_231,plain,(
    ! [B_56] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_56),k6_tmap_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k5_tmap_1('#skF_1',B_56),k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_219])).

tff(c_232,plain,(
    ! [B_56] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_56),k6_tmap_1('#skF_1','#skF_2'))
      | ~ r1_tarski(k5_tmap_1('#skF_1',B_56),k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_231])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k5_tmap_1(A_15,B_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_406,plain,(
    ! [B_82,A_83] :
      ( v1_tops_2(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_83),u1_pre_topc(A_83))))))
      | ~ v1_tops_2(B_82,g1_pre_topc(u1_struct_0(A_83),u1_pre_topc(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_422,plain,(
    ! [B_82] :
      ( v1_tops_2(B_82,'#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
      | ~ v1_tops_2(B_82,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_406])).

tff(c_430,plain,(
    ! [B_82] :
      ( v1_tops_2(B_82,'#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_82,k6_tmap_1('#skF_1','#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_68,c_128,c_422])).

tff(c_432,plain,(
    ! [B_84] :
      ( v1_tops_2(B_84,'#skF_1')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_84,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_430])).

tff(c_436,plain,(
    ! [B_16] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_16),'#skF_1')
      | ~ v1_tops_2(k5_tmap_1('#skF_1',B_16),k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_432])).

tff(c_439,plain,(
    ! [B_16] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_16),'#skF_1')
      | ~ v1_tops_2(k5_tmap_1('#skF_1',B_16),k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_436])).

tff(c_441,plain,(
    ! [B_85] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_85),'#skF_1')
      | ~ v1_tops_2(k5_tmap_1('#skF_1',B_85),k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_439])).

tff(c_450,plain,(
    ! [B_86] :
      ( v1_tops_2(k5_tmap_1('#skF_1',B_86),'#skF_1')
      | ~ r1_tarski(k5_tmap_1('#skF_1',B_86),k5_tmap_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_232,c_441])).

tff(c_457,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_450])).

tff(c_461,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_457])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( r1_tarski(B_8,u1_pre_topc(A_6))
      | ~ v1_tops_2(B_8,A_6)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_233,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k5_tmap_1(A_55,B_56),u1_pre_topc(A_55))
      | ~ v1_tops_2(k5_tmap_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_215,c_14])).

tff(c_117,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(u1_pre_topc(A_46),k5_tmap_1(A_46,B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_366,plain,(
    ! [A_76,B_77] :
      ( k5_tmap_1(A_76,B_77) = u1_pre_topc(A_76)
      | ~ r1_tarski(k5_tmap_1(A_76,B_77),u1_pre_topc(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_373,plain,(
    ! [A_55,B_56] :
      ( k5_tmap_1(A_55,B_56) = u1_pre_topc(A_55)
      | ~ v1_tops_2(k5_tmap_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_233,c_366])).

tff(c_463,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_461,c_373])).

tff(c_466,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_463])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_294,c_466])).

tff(c_470,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_469,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_473,plain,(
    ! [B_87,A_88] :
      ( r2_hidden(B_87,u1_pre_topc(A_88))
      | ~ v3_pre_topc(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_476,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_473])).

tff(c_479,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_469,c_476])).

tff(c_686,plain,(
    ! [A_123,B_124] :
      ( k5_tmap_1(A_123,B_124) = u1_pre_topc(A_123)
      | ~ r2_hidden(B_124,u1_pre_topc(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_692,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_686])).

tff(c_697,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_479,c_692])).

tff(c_698,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_697])).

tff(c_671,plain,(
    ! [A_121,B_122] :
      ( g1_pre_topc(u1_struct_0(A_121),k5_tmap_1(A_121,B_122)) = k6_tmap_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_675,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_671])).

tff(c_680,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_675])).

tff(c_681,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_680])).

tff(c_699,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_681])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.45  
% 3.09/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.45  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.09/1.45  
% 3.09/1.45  %Foreground sorts:
% 3.09/1.45  
% 3.09/1.45  
% 3.09/1.45  %Background operators:
% 3.09/1.45  
% 3.09/1.45  
% 3.09/1.45  %Foreground operators:
% 3.09/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.09/1.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.09/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.09/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.09/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.45  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.09/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.09/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.09/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.45  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.09/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.09/1.45  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.09/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.09/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.45  
% 3.09/1.47  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.09/1.47  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.09/1.47  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.09/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.47  tff(f_88, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k5_tmap_1(A, B), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_tmap_1)).
% 3.09/1.47  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.09/1.47  tff(f_103, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.09/1.47  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 3.09/1.47  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_compts_1)).
% 3.09/1.47  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(u1_pre_topc(A), k5_tmap_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_tmap_1)).
% 3.09/1.47  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.09/1.47  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.09/1.47  tff(c_58, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.09/1.47  tff(c_68, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 3.09/1.47  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.09/1.47  tff(c_74, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_52])).
% 3.09/1.47  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.09/1.47  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.09/1.47  tff(c_75, plain, (![B_32, A_33]: (v3_pre_topc(B_32, A_33) | ~r2_hidden(B_32, u1_pre_topc(A_33)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.09/1.47  tff(c_78, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_75])).
% 3.09/1.47  tff(c_81, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_78])).
% 3.09/1.47  tff(c_82, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_74, c_81])).
% 3.09/1.47  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.09/1.47  tff(c_282, plain, (![B_64, A_65]: (r2_hidden(B_64, u1_pre_topc(A_65)) | k5_tmap_1(A_65, B_64)!=u1_pre_topc(A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.09/1.47  tff(c_288, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_282])).
% 3.09/1.47  tff(c_293, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_288])).
% 3.09/1.47  tff(c_294, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_82, c_293])).
% 3.09/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.47  tff(c_215, plain, (![A_55, B_56]: (m1_subset_1(k5_tmap_1(A_55, B_56), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.09/1.47  tff(c_174, plain, (![A_50, B_51]: (u1_pre_topc(k6_tmap_1(A_50, B_51))=k5_tmap_1(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.09/1.47  tff(c_180, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_174])).
% 3.09/1.47  tff(c_185, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_180])).
% 3.09/1.47  tff(c_186, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_185])).
% 3.09/1.47  tff(c_92, plain, (![A_38, B_39]: (l1_pre_topc(k6_tmap_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.09/1.47  tff(c_95, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_92])).
% 3.09/1.47  tff(c_98, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_95])).
% 3.09/1.47  tff(c_99, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_98])).
% 3.09/1.47  tff(c_121, plain, (![A_48, B_49]: (u1_struct_0(k6_tmap_1(A_48, B_49))=u1_struct_0(A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.09/1.47  tff(c_124, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_121])).
% 3.09/1.47  tff(c_127, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_124])).
% 3.09/1.47  tff(c_128, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_127])).
% 3.09/1.47  tff(c_12, plain, (![B_8, A_6]: (v1_tops_2(B_8, A_6) | ~r1_tarski(B_8, u1_pre_topc(A_6)) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.47  tff(c_147, plain, (![B_8]: (v1_tops_2(B_8, k6_tmap_1('#skF_1', '#skF_2')) | ~r1_tarski(B_8, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_12])).
% 3.09/1.47  tff(c_167, plain, (![B_8]: (v1_tops_2(B_8, k6_tmap_1('#skF_1', '#skF_2')) | ~r1_tarski(B_8, u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_147])).
% 3.09/1.47  tff(c_213, plain, (![B_8]: (v1_tops_2(B_8, k6_tmap_1('#skF_1', '#skF_2')) | ~r1_tarski(B_8, k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_167])).
% 3.09/1.47  tff(c_219, plain, (![B_56]: (v1_tops_2(k5_tmap_1('#skF_1', B_56), k6_tmap_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_tmap_1('#skF_1', B_56), k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_215, c_213])).
% 3.09/1.47  tff(c_231, plain, (![B_56]: (v1_tops_2(k5_tmap_1('#skF_1', B_56), k6_tmap_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_tmap_1('#skF_1', B_56), k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_219])).
% 3.09/1.47  tff(c_232, plain, (![B_56]: (v1_tops_2(k5_tmap_1('#skF_1', B_56), k6_tmap_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_tmap_1('#skF_1', B_56), k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_231])).
% 3.09/1.47  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(k5_tmap_1(A_15, B_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.09/1.47  tff(c_406, plain, (![B_82, A_83]: (v1_tops_2(B_82, A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_83), u1_pre_topc(A_83)))))) | ~v1_tops_2(B_82, g1_pre_topc(u1_struct_0(A_83), u1_pre_topc(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.47  tff(c_422, plain, (![B_82]: (v1_tops_2(B_82, '#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~v1_tops_2(B_82, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_406])).
% 3.09/1.47  tff(c_430, plain, (![B_82]: (v1_tops_2(B_82, '#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_82, k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_68, c_128, c_422])).
% 3.09/1.47  tff(c_432, plain, (![B_84]: (v1_tops_2(B_84, '#skF_1') | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_84, k6_tmap_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_430])).
% 3.09/1.47  tff(c_436, plain, (![B_16]: (v1_tops_2(k5_tmap_1('#skF_1', B_16), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', B_16), k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_432])).
% 3.09/1.47  tff(c_439, plain, (![B_16]: (v1_tops_2(k5_tmap_1('#skF_1', B_16), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', B_16), k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_436])).
% 3.09/1.47  tff(c_441, plain, (![B_85]: (v1_tops_2(k5_tmap_1('#skF_1', B_85), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', B_85), k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_439])).
% 3.09/1.47  tff(c_450, plain, (![B_86]: (v1_tops_2(k5_tmap_1('#skF_1', B_86), '#skF_1') | ~r1_tarski(k5_tmap_1('#skF_1', B_86), k5_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_232, c_441])).
% 3.09/1.47  tff(c_457, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_450])).
% 3.09/1.47  tff(c_461, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_457])).
% 3.09/1.47  tff(c_14, plain, (![B_8, A_6]: (r1_tarski(B_8, u1_pre_topc(A_6)) | ~v1_tops_2(B_8, A_6) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.47  tff(c_233, plain, (![A_55, B_56]: (r1_tarski(k5_tmap_1(A_55, B_56), u1_pre_topc(A_55)) | ~v1_tops_2(k5_tmap_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_215, c_14])).
% 3.09/1.47  tff(c_117, plain, (![A_46, B_47]: (r1_tarski(u1_pre_topc(A_46), k5_tmap_1(A_46, B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.09/1.47  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.47  tff(c_366, plain, (![A_76, B_77]: (k5_tmap_1(A_76, B_77)=u1_pre_topc(A_76) | ~r1_tarski(k5_tmap_1(A_76, B_77), u1_pre_topc(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_117, c_2])).
% 3.09/1.47  tff(c_373, plain, (![A_55, B_56]: (k5_tmap_1(A_55, B_56)=u1_pre_topc(A_55) | ~v1_tops_2(k5_tmap_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_233, c_366])).
% 3.09/1.47  tff(c_463, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_461, c_373])).
% 3.09/1.47  tff(c_466, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_463])).
% 3.09/1.47  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_294, c_466])).
% 3.09/1.47  tff(c_470, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.09/1.47  tff(c_469, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 3.09/1.47  tff(c_473, plain, (![B_87, A_88]: (r2_hidden(B_87, u1_pre_topc(A_88)) | ~v3_pre_topc(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.09/1.47  tff(c_476, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_473])).
% 3.09/1.47  tff(c_479, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_469, c_476])).
% 3.09/1.47  tff(c_686, plain, (![A_123, B_124]: (k5_tmap_1(A_123, B_124)=u1_pre_topc(A_123) | ~r2_hidden(B_124, u1_pre_topc(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.09/1.47  tff(c_692, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_686])).
% 3.09/1.47  tff(c_697, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_479, c_692])).
% 3.09/1.47  tff(c_698, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_697])).
% 3.09/1.47  tff(c_671, plain, (![A_121, B_122]: (g1_pre_topc(u1_struct_0(A_121), k5_tmap_1(A_121, B_122))=k6_tmap_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.09/1.47  tff(c_675, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_671])).
% 3.09/1.47  tff(c_680, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_675])).
% 3.09/1.47  tff(c_681, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_680])).
% 3.09/1.47  tff(c_699, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_698, c_681])).
% 3.09/1.47  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_699])).
% 3.09/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.47  
% 3.09/1.47  Inference rules
% 3.09/1.47  ----------------------
% 3.09/1.47  #Ref     : 0
% 3.09/1.47  #Sup     : 111
% 3.09/1.47  #Fact    : 0
% 3.09/1.47  #Define  : 0
% 3.09/1.47  #Split   : 5
% 3.09/1.47  #Chain   : 0
% 3.09/1.47  #Close   : 0
% 3.09/1.47  
% 3.09/1.47  Ordering : KBO
% 3.09/1.47  
% 3.09/1.47  Simplification rules
% 3.09/1.47  ----------------------
% 3.09/1.47  #Subsume      : 4
% 3.09/1.47  #Demod        : 228
% 3.09/1.47  #Tautology    : 57
% 3.09/1.47  #SimpNegUnit  : 31
% 3.09/1.47  #BackRed      : 13
% 3.09/1.47  
% 3.09/1.47  #Partial instantiations: 0
% 3.09/1.47  #Strategies tried      : 1
% 3.09/1.47  
% 3.09/1.47  Timing (in seconds)
% 3.09/1.47  ----------------------
% 3.09/1.47  Preprocessing        : 0.34
% 3.09/1.47  Parsing              : 0.18
% 3.09/1.47  CNF conversion       : 0.02
% 3.09/1.47  Main loop            : 0.35
% 3.09/1.47  Inferencing          : 0.13
% 3.09/1.47  Reduction            : 0.12
% 3.09/1.47  Demodulation         : 0.08
% 3.09/1.47  BG Simplification    : 0.02
% 3.09/1.47  Subsumption          : 0.07
% 3.09/1.47  Abstraction          : 0.02
% 3.09/1.47  MUC search           : 0.00
% 3.09/1.47  Cooper               : 0.00
% 3.09/1.47  Total                : 0.74
% 3.09/1.47  Index Insertion      : 0.00
% 3.09/1.47  Index Deletion       : 0.00
% 3.09/1.47  Index Matching       : 0.00
% 3.09/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
