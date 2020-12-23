%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 843 expanded)
%              Number of leaves         :   37 ( 305 expanded)
%              Depth                    :   25
%              Number of atoms          :  388 (2425 expanded)
%              Number of equality atoms :   60 ( 306 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_73,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k6_tmap_1('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_69,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_347,plain,(
    ! [B_78,A_79] :
      ( v3_pre_topc(B_78,A_79)
      | ~ r2_hidden(B_78,u1_pre_topc(A_79))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_354,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4',u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_347])).

tff(c_362,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_354])).

tff(c_363,plain,(
    ~ r2_hidden('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_362])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1304,plain,(
    ! [B_153,A_154] :
      ( r2_hidden(B_153,u1_pre_topc(A_154))
      | k5_tmap_1(A_154,B_153) != u1_pre_topc(A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1321,plain,
    ( r2_hidden('#skF_4',u1_pre_topc('#skF_3'))
    | k5_tmap_1('#skF_3','#skF_4') != u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1304])).

tff(c_1332,plain,
    ( r2_hidden('#skF_4',u1_pre_topc('#skF_3'))
    | k5_tmap_1('#skF_3','#skF_4') != u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1321])).

tff(c_1333,plain,(
    k5_tmap_1('#skF_3','#skF_4') != u1_pre_topc('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_363,c_1332])).

tff(c_1125,plain,(
    ! [A_144,B_145] :
      ( u1_pre_topc(k6_tmap_1(A_144,B_145)) = k5_tmap_1(A_144,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1142,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1125])).

tff(c_1153,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1142])).

tff(c_1154,plain,(
    u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1153])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,(
    ! [A_10,A_50] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_88])).

tff(c_108,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_113,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_235,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tops_1(A_65,B_66),B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_253,plain,(
    ! [A_67] :
      ( r1_tarski(k1_tops_1(A_67,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_18,c_235])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_258,plain,(
    ! [A_67] :
      ( k1_tops_1(A_67,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_tops_1(A_67,k1_xboole_0))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_253,c_8])).

tff(c_264,plain,(
    ! [A_68] :
      ( k1_tops_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_258])).

tff(c_268,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_264])).

tff(c_443,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k1_tops_1(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_484,plain,(
    ! [A_92] :
      ( v3_pre_topc(k1_tops_1(A_92,k1_xboole_0),A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_18,c_443])).

tff(c_487,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_484])).

tff(c_489,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_487])).

tff(c_290,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,u1_pre_topc(A_72))
      | ~ v3_pre_topc(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_306,plain,(
    ! [A_72] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_72))
      | ~ v3_pre_topc(k1_xboole_0,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_18,c_290])).

tff(c_1198,plain,(
    ! [A_147,B_148] :
      ( k5_tmap_1(A_147,B_148) = u1_pre_topc(A_147)
      | ~ r2_hidden(B_148,u1_pre_topc(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1577,plain,(
    ! [A_168] :
      ( k5_tmap_1(A_168,k1_xboole_0) = u1_pre_topc(A_168)
      | ~ r2_hidden(k1_xboole_0,u1_pre_topc(A_168))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_18,c_1198])).

tff(c_1590,plain,(
    ! [A_169] :
      ( k5_tmap_1(A_169,k1_xboole_0) = u1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ v3_pre_topc(k1_xboole_0,A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_306,c_1577])).

tff(c_1596,plain,
    ( k5_tmap_1('#skF_3',k1_xboole_0) = u1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_489,c_1590])).

tff(c_1602,plain,
    ( k5_tmap_1('#skF_3',k1_xboole_0) = u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1596])).

tff(c_1603,plain,(
    k5_tmap_1('#skF_3',k1_xboole_0) = u1_pre_topc('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1602])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_118,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_62])).

tff(c_854,plain,(
    ! [A_138,B_139] :
      ( u1_struct_0(k6_tmap_1(A_138,B_139)) = u1_struct_0(A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_876,plain,(
    ! [A_138] :
      ( u1_struct_0(k6_tmap_1(A_138,k1_xboole_0)) = u1_struct_0(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_18,c_854])).

tff(c_792,plain,(
    ! [A_130,B_131] :
      ( v1_pre_topc(k6_tmap_1(A_130,B_131))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_814,plain,(
    ! [A_130] :
      ( v1_pre_topc(k6_tmap_1(A_130,k1_xboole_0))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_18,c_792])).

tff(c_564,plain,(
    ! [A_102,B_103] :
      ( l1_pre_topc(k6_tmap_1(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_586,plain,(
    ! [A_102] :
      ( l1_pre_topc(k6_tmap_1(A_102,k1_xboole_0))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_18,c_564])).

tff(c_742,plain,(
    ! [A_123,B_124] :
      ( v2_pre_topc(k6_tmap_1(A_123,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_764,plain,(
    ! [A_123] :
      ( v2_pre_topc(k6_tmap_1(A_123,k1_xboole_0))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_18,c_742])).

tff(c_717,plain,(
    ! [A_119] :
      ( l1_pre_topc(k6_tmap_1(A_119,k1_xboole_0))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_18,c_564])).

tff(c_262,plain,(
    ! [A_67] :
      ( k1_tops_1(A_67,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_258])).

tff(c_1106,plain,(
    ! [A_143] :
      ( k1_tops_1(k6_tmap_1(A_143,k1_xboole_0),k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_717,c_262])).

tff(c_460,plain,(
    ! [A_88] :
      ( v3_pre_topc(k1_tops_1(A_88,k1_xboole_0),A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_18,c_443])).

tff(c_1115,plain,(
    ! [A_143] :
      ( v3_pre_topc(k1_xboole_0,k6_tmap_1(A_143,k1_xboole_0))
      | ~ l1_pre_topc(k6_tmap_1(A_143,k1_xboole_0))
      | ~ v2_pre_topc(k6_tmap_1(A_143,k1_xboole_0))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_460])).

tff(c_1254,plain,(
    ! [A_151] :
      ( u1_pre_topc(k6_tmap_1(A_151,k1_xboole_0)) = k5_tmap_1(A_151,k1_xboole_0)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_18,c_1125])).

tff(c_3578,plain,(
    ! [A_294] :
      ( r2_hidden(k1_xboole_0,k5_tmap_1(A_294,k1_xboole_0))
      | ~ v3_pre_topc(k1_xboole_0,k6_tmap_1(A_294,k1_xboole_0))
      | ~ l1_pre_topc(k6_tmap_1(A_294,k1_xboole_0))
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1254,c_306])).

tff(c_3591,plain,(
    ! [A_295] :
      ( r2_hidden(k1_xboole_0,k5_tmap_1(A_295,k1_xboole_0))
      | ~ l1_pre_topc(k6_tmap_1(A_295,k1_xboole_0))
      | ~ v2_pre_topc(k6_tmap_1(A_295,k1_xboole_0))
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_1115,c_3578])).

tff(c_3596,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1603,c_3591])).

tff(c_3599,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3596])).

tff(c_3600,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3599])).

tff(c_3601,plain,(
    ~ v2_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3600])).

tff(c_3604,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_764,c_3601])).

tff(c_3607,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3604])).

tff(c_3609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3607])).

tff(c_3610,plain,
    ( ~ l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | r2_hidden(k1_xboole_0,u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3600])).

tff(c_3612,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3610])).

tff(c_3615,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_586,c_3612])).

tff(c_3618,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3615])).

tff(c_3620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3618])).

tff(c_3622,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3610])).

tff(c_24,plain,(
    ! [A_17] :
      ( g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)) = A_17
      | ~ v1_pre_topc(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5090,plain,(
    ! [A_350] :
      ( g1_pre_topc(u1_struct_0(k6_tmap_1(A_350,k1_xboole_0)),k5_tmap_1(A_350,k1_xboole_0)) = k6_tmap_1(A_350,k1_xboole_0)
      | ~ v1_pre_topc(k6_tmap_1(A_350,k1_xboole_0))
      | ~ l1_pre_topc(k6_tmap_1(A_350,k1_xboole_0))
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1254,c_24])).

tff(c_5099,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3',k1_xboole_0)),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',k1_xboole_0)
    | ~ v1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1603,c_5090])).

tff(c_5106,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3',k1_xboole_0)),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',k1_xboole_0)
    | ~ v1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3622,c_5099])).

tff(c_5107,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3',k1_xboole_0)),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',k1_xboole_0)
    | ~ v1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5106])).

tff(c_5108,plain,(
    ~ v1_pre_topc(k6_tmap_1('#skF_3',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_5107])).

tff(c_5111,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_814,c_5108])).

tff(c_5114,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5111])).

tff(c_5116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5114])).

tff(c_5117,plain,(
    g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3',k1_xboole_0)),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5107])).

tff(c_5123,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3',k1_xboole_0)
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_5117])).

tff(c_5127,plain,
    ( k6_tmap_1('#skF_3',k1_xboole_0) = k6_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_118,c_5123])).

tff(c_5128,plain,(
    k6_tmap_1('#skF_3',k1_xboole_0) = k6_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5127])).

tff(c_1155,plain,(
    ! [A_144] :
      ( u1_pre_topc(k6_tmap_1(A_144,k1_xboole_0)) = k5_tmap_1(A_144,k1_xboole_0)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_18,c_1125])).

tff(c_5176,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3',k1_xboole_0)
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5128,c_1155])).

tff(c_5225,plain,
    ( k5_tmap_1('#skF_3','#skF_4') = u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1154,c_1603,c_5176])).

tff(c_5227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1333,c_5225])).

tff(c_5228,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_14,plain,(
    ! [A_8] : v1_xboole_0('#skF_2'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5228,c_14])).

tff(c_5231,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k6_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5232,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5444,plain,(
    ! [B_381,A_382] :
      ( r2_hidden(B_381,u1_pre_topc(A_382))
      | ~ v3_pre_topc(B_381,A_382)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_382)))
      | ~ l1_pre_topc(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5451,plain,
    ( r2_hidden('#skF_4',u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_5444])).

tff(c_5459,plain,(
    r2_hidden('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5232,c_5451])).

tff(c_6372,plain,(
    ! [A_454,B_455] :
      ( k5_tmap_1(A_454,B_455) = u1_pre_topc(A_454)
      | ~ r2_hidden(B_455,u1_pre_topc(A_454))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6389,plain,
    ( k5_tmap_1('#skF_3','#skF_4') = u1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_4',u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_6372])).

tff(c_6400,plain,
    ( k5_tmap_1('#skF_3','#skF_4') = u1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5459,c_6389])).

tff(c_6401,plain,(
    k5_tmap_1('#skF_3','#skF_4') = u1_pre_topc('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6400])).

tff(c_5691,plain,(
    ! [A_408,B_409] :
      ( l1_pre_topc(k6_tmap_1(A_408,B_409))
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5702,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_5691])).

tff(c_5711,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5702])).

tff(c_5712,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5711])).

tff(c_5822,plain,(
    ! [A_421,B_422] :
      ( v1_pre_topc(k6_tmap_1(A_421,B_422))
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5833,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_5822])).

tff(c_5842,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5833])).

tff(c_5843,plain,(
    v1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5842])).

tff(c_5924,plain,(
    ! [A_434,B_435] :
      ( u1_struct_0(k6_tmap_1(A_434,B_435)) = u1_struct_0(A_434)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5935,plain,
    ( u1_struct_0(k6_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_5924])).

tff(c_5944,plain,
    ( u1_struct_0(k6_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5935])).

tff(c_5945,plain,(
    u1_struct_0(k6_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5944])).

tff(c_6034,plain,(
    ! [A_436,B_437] :
      ( u1_pre_topc(k6_tmap_1(A_436,B_437)) = k5_tmap_1(A_436,B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6048,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_6034])).

tff(c_6059,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_6048])).

tff(c_6060,plain,(
    u1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) = k5_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6059])).

tff(c_6072,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3','#skF_4')),k5_tmap_1('#skF_3','#skF_4')) = k6_tmap_1('#skF_3','#skF_4')
    | ~ v1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6060,c_24])).

tff(c_6080,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),k5_tmap_1('#skF_3','#skF_4')) = k6_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5712,c_5843,c_5945,c_6072])).

tff(c_6403,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k6_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6401,c_6080])).

tff(c_6408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5231,c_6403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.56/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.54  
% 7.56/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.54  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.56/2.54  
% 7.56/2.54  %Foreground sorts:
% 7.56/2.54  
% 7.56/2.54  
% 7.56/2.54  %Background operators:
% 7.56/2.54  
% 7.56/2.54  
% 7.56/2.54  %Foreground operators:
% 7.56/2.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.56/2.54  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.56/2.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.56/2.54  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.56/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.54  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.56/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.56/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.56/2.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.56/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.56/2.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.56/2.54  tff('#skF_3', type, '#skF_3': $i).
% 7.56/2.54  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.56/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.54  tff('#skF_4', type, '#skF_4': $i).
% 7.56/2.54  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 7.56/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.56/2.54  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 7.56/2.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.56/2.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.56/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.56/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.54  
% 7.56/2.56  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 7.56/2.56  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 7.56/2.56  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 7.56/2.56  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 7.56/2.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.56/2.56  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.56/2.56  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.56/2.56  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.56/2.56  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.56/2.56  tff(f_81, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.56/2.56  tff(f_103, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 7.56/2.56  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 7.56/2.56  tff(f_43, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 7.56/2.56  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.56/2.56  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k6_tmap_1('#skF_3', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.56/2.56  tff(c_69, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 7.56/2.56  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.56/2.56  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.56/2.56  tff(c_347, plain, (![B_78, A_79]: (v3_pre_topc(B_78, A_79) | ~r2_hidden(B_78, u1_pre_topc(A_79)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.56/2.56  tff(c_354, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_347])).
% 7.56/2.56  tff(c_362, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_354])).
% 7.56/2.56  tff(c_363, plain, (~r2_hidden('#skF_4', u1_pre_topc('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_69, c_362])).
% 7.56/2.56  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.56/2.56  tff(c_1304, plain, (![B_153, A_154]: (r2_hidden(B_153, u1_pre_topc(A_154)) | k5_tmap_1(A_154, B_153)!=u1_pre_topc(A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.56/2.56  tff(c_1321, plain, (r2_hidden('#skF_4', u1_pre_topc('#skF_3')) | k5_tmap_1('#skF_3', '#skF_4')!=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1304])).
% 7.56/2.56  tff(c_1332, plain, (r2_hidden('#skF_4', u1_pre_topc('#skF_3')) | k5_tmap_1('#skF_3', '#skF_4')!=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1321])).
% 7.56/2.56  tff(c_1333, plain, (k5_tmap_1('#skF_3', '#skF_4')!=u1_pre_topc('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_363, c_1332])).
% 7.56/2.56  tff(c_1125, plain, (![A_144, B_145]: (u1_pre_topc(k6_tmap_1(A_144, B_145))=k5_tmap_1(A_144, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.56/2.56  tff(c_1142, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1125])).
% 7.56/2.56  tff(c_1153, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1142])).
% 7.56/2.56  tff(c_1154, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_1153])).
% 7.56/2.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.56/2.56  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.56/2.56  tff(c_88, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.56/2.56  tff(c_97, plain, (![A_10, A_50]: (~v1_xboole_0(A_10) | ~r2_hidden(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_88])).
% 7.56/2.56  tff(c_108, plain, (![A_52]: (~r2_hidden(A_52, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_97])).
% 7.56/2.56  tff(c_113, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_108])).
% 7.56/2.56  tff(c_235, plain, (![A_65, B_66]: (r1_tarski(k1_tops_1(A_65, B_66), B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.56/2.56  tff(c_253, plain, (![A_67]: (r1_tarski(k1_tops_1(A_67, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_18, c_235])).
% 7.56/2.56  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.56/2.56  tff(c_258, plain, (![A_67]: (k1_tops_1(A_67, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tops_1(A_67, k1_xboole_0)) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_253, c_8])).
% 7.56/2.56  tff(c_264, plain, (![A_68]: (k1_tops_1(A_68, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_258])).
% 7.56/2.56  tff(c_268, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_264])).
% 7.56/2.56  tff(c_443, plain, (![A_88, B_89]: (v3_pre_topc(k1_tops_1(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.56/2.56  tff(c_484, plain, (![A_92]: (v3_pre_topc(k1_tops_1(A_92, k1_xboole_0), A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(resolution, [status(thm)], [c_18, c_443])).
% 7.56/2.56  tff(c_487, plain, (v3_pre_topc(k1_xboole_0, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_268, c_484])).
% 7.56/2.56  tff(c_489, plain, (v3_pre_topc(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_487])).
% 7.56/2.56  tff(c_290, plain, (![B_71, A_72]: (r2_hidden(B_71, u1_pre_topc(A_72)) | ~v3_pre_topc(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.56/2.56  tff(c_306, plain, (![A_72]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_72)) | ~v3_pre_topc(k1_xboole_0, A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_18, c_290])).
% 7.56/2.56  tff(c_1198, plain, (![A_147, B_148]: (k5_tmap_1(A_147, B_148)=u1_pre_topc(A_147) | ~r2_hidden(B_148, u1_pre_topc(A_147)) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.56/2.56  tff(c_1577, plain, (![A_168]: (k5_tmap_1(A_168, k1_xboole_0)=u1_pre_topc(A_168) | ~r2_hidden(k1_xboole_0, u1_pre_topc(A_168)) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_18, c_1198])).
% 7.56/2.56  tff(c_1590, plain, (![A_169]: (k5_tmap_1(A_169, k1_xboole_0)=u1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~v3_pre_topc(k1_xboole_0, A_169) | ~l1_pre_topc(A_169))), inference(resolution, [status(thm)], [c_306, c_1577])).
% 7.56/2.56  tff(c_1596, plain, (k5_tmap_1('#skF_3', k1_xboole_0)=u1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_489, c_1590])).
% 7.56/2.56  tff(c_1602, plain, (k5_tmap_1('#skF_3', k1_xboole_0)=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1596])).
% 7.56/2.56  tff(c_1603, plain, (k5_tmap_1('#skF_3', k1_xboole_0)=u1_pre_topc('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_1602])).
% 7.56/2.56  tff(c_62, plain, (v3_pre_topc('#skF_4', '#skF_3') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.56/2.56  tff(c_118, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_69, c_62])).
% 7.56/2.56  tff(c_854, plain, (![A_138, B_139]: (u1_struct_0(k6_tmap_1(A_138, B_139))=u1_struct_0(A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.56/2.56  tff(c_876, plain, (![A_138]: (u1_struct_0(k6_tmap_1(A_138, k1_xboole_0))=u1_struct_0(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_18, c_854])).
% 7.56/2.56  tff(c_792, plain, (![A_130, B_131]: (v1_pre_topc(k6_tmap_1(A_130, B_131)) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.56/2.56  tff(c_814, plain, (![A_130]: (v1_pre_topc(k6_tmap_1(A_130, k1_xboole_0)) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_18, c_792])).
% 7.56/2.56  tff(c_564, plain, (![A_102, B_103]: (l1_pre_topc(k6_tmap_1(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.56/2.56  tff(c_586, plain, (![A_102]: (l1_pre_topc(k6_tmap_1(A_102, k1_xboole_0)) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_18, c_564])).
% 7.56/2.56  tff(c_742, plain, (![A_123, B_124]: (v2_pre_topc(k6_tmap_1(A_123, B_124)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.56/2.56  tff(c_764, plain, (![A_123]: (v2_pre_topc(k6_tmap_1(A_123, k1_xboole_0)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_18, c_742])).
% 7.56/2.56  tff(c_717, plain, (![A_119]: (l1_pre_topc(k6_tmap_1(A_119, k1_xboole_0)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_18, c_564])).
% 7.56/2.56  tff(c_262, plain, (![A_67]: (k1_tops_1(A_67, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_258])).
% 7.56/2.56  tff(c_1106, plain, (![A_143]: (k1_tops_1(k6_tmap_1(A_143, k1_xboole_0), k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_717, c_262])).
% 7.56/2.56  tff(c_460, plain, (![A_88]: (v3_pre_topc(k1_tops_1(A_88, k1_xboole_0), A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(resolution, [status(thm)], [c_18, c_443])).
% 7.56/2.56  tff(c_1115, plain, (![A_143]: (v3_pre_topc(k1_xboole_0, k6_tmap_1(A_143, k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(A_143, k1_xboole_0)) | ~v2_pre_topc(k6_tmap_1(A_143, k1_xboole_0)) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_460])).
% 7.56/2.56  tff(c_1254, plain, (![A_151]: (u1_pre_topc(k6_tmap_1(A_151, k1_xboole_0))=k5_tmap_1(A_151, k1_xboole_0) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_18, c_1125])).
% 7.56/2.56  tff(c_3578, plain, (![A_294]: (r2_hidden(k1_xboole_0, k5_tmap_1(A_294, k1_xboole_0)) | ~v3_pre_topc(k1_xboole_0, k6_tmap_1(A_294, k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(A_294, k1_xboole_0)) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(superposition, [status(thm), theory('equality')], [c_1254, c_306])).
% 7.56/2.56  tff(c_3591, plain, (![A_295]: (r2_hidden(k1_xboole_0, k5_tmap_1(A_295, k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(A_295, k1_xboole_0)) | ~v2_pre_topc(k6_tmap_1(A_295, k1_xboole_0)) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(resolution, [status(thm)], [c_1115, c_3578])).
% 7.56/2.56  tff(c_3596, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | ~v2_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1603, c_3591])).
% 7.56/2.56  tff(c_3599, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | ~v2_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3596])).
% 7.56/2.56  tff(c_3600, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | ~v2_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_54, c_3599])).
% 7.56/2.56  tff(c_3601, plain, (~v2_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3600])).
% 7.56/2.56  tff(c_3604, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_764, c_3601])).
% 7.56/2.56  tff(c_3607, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3604])).
% 7.56/2.56  tff(c_3609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3607])).
% 7.56/2.56  tff(c_3610, plain, (~l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | r2_hidden(k1_xboole_0, u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_3600])).
% 7.56/2.56  tff(c_3612, plain, (~l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3610])).
% 7.56/2.56  tff(c_3615, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_586, c_3612])).
% 7.56/2.56  tff(c_3618, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3615])).
% 7.56/2.56  tff(c_3620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3618])).
% 7.56/2.56  tff(c_3622, plain, (l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0))), inference(splitRight, [status(thm)], [c_3610])).
% 7.56/2.56  tff(c_24, plain, (![A_17]: (g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17))=A_17 | ~v1_pre_topc(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.56/2.56  tff(c_5090, plain, (![A_350]: (g1_pre_topc(u1_struct_0(k6_tmap_1(A_350, k1_xboole_0)), k5_tmap_1(A_350, k1_xboole_0))=k6_tmap_1(A_350, k1_xboole_0) | ~v1_pre_topc(k6_tmap_1(A_350, k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(A_350, k1_xboole_0)) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(superposition, [status(thm), theory('equality')], [c_1254, c_24])).
% 7.56/2.56  tff(c_5099, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', k1_xboole_0)), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', k1_xboole_0) | ~v1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1603, c_5090])).
% 7.56/2.56  tff(c_5106, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', k1_xboole_0)), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', k1_xboole_0) | ~v1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0)) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3622, c_5099])).
% 7.56/2.56  tff(c_5107, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', k1_xboole_0)), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', k1_xboole_0) | ~v1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_54, c_5106])).
% 7.56/2.56  tff(c_5108, plain, (~v1_pre_topc(k6_tmap_1('#skF_3', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_5107])).
% 7.56/2.56  tff(c_5111, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_814, c_5108])).
% 7.56/2.56  tff(c_5114, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5111])).
% 7.56/2.56  tff(c_5116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5114])).
% 7.56/2.56  tff(c_5117, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', k1_xboole_0)), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5107])).
% 7.56/2.56  tff(c_5123, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', k1_xboole_0) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_876, c_5117])).
% 7.56/2.56  tff(c_5127, plain, (k6_tmap_1('#skF_3', k1_xboole_0)=k6_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_118, c_5123])).
% 7.56/2.56  tff(c_5128, plain, (k6_tmap_1('#skF_3', k1_xboole_0)=k6_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_5127])).
% 7.56/2.56  tff(c_1155, plain, (![A_144]: (u1_pre_topc(k6_tmap_1(A_144, k1_xboole_0))=k5_tmap_1(A_144, k1_xboole_0) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_18, c_1125])).
% 7.56/2.56  tff(c_5176, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', k1_xboole_0) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5128, c_1155])).
% 7.56/2.56  tff(c_5225, plain, (k5_tmap_1('#skF_3', '#skF_4')=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1154, c_1603, c_5176])).
% 7.56/2.56  tff(c_5227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1333, c_5225])).
% 7.56/2.56  tff(c_5228, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitRight, [status(thm)], [c_97])).
% 7.56/2.56  tff(c_14, plain, (![A_8]: (v1_xboole_0('#skF_2'(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.56/2.56  tff(c_5230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5228, c_14])).
% 7.56/2.56  tff(c_5231, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k6_tmap_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 7.56/2.56  tff(c_5232, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 7.56/2.56  tff(c_5444, plain, (![B_381, A_382]: (r2_hidden(B_381, u1_pre_topc(A_382)) | ~v3_pre_topc(B_381, A_382) | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0(A_382))) | ~l1_pre_topc(A_382))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.56/2.56  tff(c_5451, plain, (r2_hidden('#skF_4', u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_5444])).
% 7.56/2.56  tff(c_5459, plain, (r2_hidden('#skF_4', u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5232, c_5451])).
% 7.56/2.56  tff(c_6372, plain, (![A_454, B_455]: (k5_tmap_1(A_454, B_455)=u1_pre_topc(A_454) | ~r2_hidden(B_455, u1_pre_topc(A_454)) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.56/2.56  tff(c_6389, plain, (k5_tmap_1('#skF_3', '#skF_4')=u1_pre_topc('#skF_3') | ~r2_hidden('#skF_4', u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_6372])).
% 7.56/2.56  tff(c_6400, plain, (k5_tmap_1('#skF_3', '#skF_4')=u1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5459, c_6389])).
% 7.56/2.56  tff(c_6401, plain, (k5_tmap_1('#skF_3', '#skF_4')=u1_pre_topc('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_6400])).
% 7.56/2.56  tff(c_5691, plain, (![A_408, B_409]: (l1_pre_topc(k6_tmap_1(A_408, B_409)) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.56/2.56  tff(c_5702, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_5691])).
% 7.56/2.56  tff(c_5711, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5702])).
% 7.56/2.56  tff(c_5712, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_5711])).
% 7.56/2.56  tff(c_5822, plain, (![A_421, B_422]: (v1_pre_topc(k6_tmap_1(A_421, B_422)) | ~m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0(A_421))) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.56/2.56  tff(c_5833, plain, (v1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_5822])).
% 7.56/2.56  tff(c_5842, plain, (v1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5833])).
% 7.56/2.56  tff(c_5843, plain, (v1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_5842])).
% 7.56/2.56  tff(c_5924, plain, (![A_434, B_435]: (u1_struct_0(k6_tmap_1(A_434, B_435))=u1_struct_0(A_434) | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0(A_434))) | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.56/2.56  tff(c_5935, plain, (u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_5924])).
% 7.56/2.56  tff(c_5944, plain, (u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5935])).
% 7.56/2.56  tff(c_5945, plain, (u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_5944])).
% 7.56/2.56  tff(c_6034, plain, (![A_436, B_437]: (u1_pre_topc(k6_tmap_1(A_436, B_437))=k5_tmap_1(A_436, B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.56/2.56  tff(c_6048, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_6034])).
% 7.56/2.56  tff(c_6059, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_6048])).
% 7.56/2.56  tff(c_6060, plain, (u1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))=k5_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_6059])).
% 7.56/2.56  tff(c_6072, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')), k5_tmap_1('#skF_3', '#skF_4'))=k6_tmap_1('#skF_3', '#skF_4') | ~v1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6060, c_24])).
% 7.56/2.56  tff(c_6080, plain, (g1_pre_topc(u1_struct_0('#skF_3'), k5_tmap_1('#skF_3', '#skF_4'))=k6_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5712, c_5843, c_5945, c_6072])).
% 7.56/2.56  tff(c_6403, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k6_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6401, c_6080])).
% 7.56/2.56  tff(c_6408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5231, c_6403])).
% 7.56/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.56  
% 7.56/2.56  Inference rules
% 7.56/2.56  ----------------------
% 7.56/2.56  #Ref     : 0
% 7.56/2.56  #Sup     : 1492
% 7.56/2.56  #Fact    : 0
% 7.56/2.56  #Define  : 0
% 7.56/2.56  #Split   : 25
% 7.56/2.56  #Chain   : 0
% 7.56/2.56  #Close   : 0
% 7.56/2.56  
% 7.56/2.56  Ordering : KBO
% 7.56/2.56  
% 7.56/2.56  Simplification rules
% 7.56/2.56  ----------------------
% 7.56/2.56  #Subsume      : 555
% 7.56/2.56  #Demod        : 912
% 7.56/2.56  #Tautology    : 309
% 7.56/2.56  #SimpNegUnit  : 64
% 7.56/2.56  #BackRed      : 16
% 7.56/2.56  
% 7.56/2.56  #Partial instantiations: 0
% 7.56/2.56  #Strategies tried      : 1
% 7.56/2.56  
% 7.56/2.56  Timing (in seconds)
% 7.56/2.56  ----------------------
% 7.56/2.57  Preprocessing        : 0.35
% 7.56/2.57  Parsing              : 0.18
% 7.56/2.57  CNF conversion       : 0.03
% 7.56/2.57  Main loop            : 1.44
% 7.56/2.57  Inferencing          : 0.48
% 7.56/2.57  Reduction            : 0.47
% 7.56/2.57  Demodulation         : 0.32
% 7.56/2.57  BG Simplification    : 0.05
% 7.56/2.57  Subsumption          : 0.33
% 7.56/2.57  Abstraction          : 0.07
% 7.56/2.57  MUC search           : 0.00
% 7.56/2.57  Cooper               : 0.00
% 7.56/2.57  Total                : 1.84
% 7.56/2.57  Index Insertion      : 0.00
% 7.56/2.57  Index Deletion       : 0.00
% 7.56/2.57  Index Matching       : 0.00
% 7.56/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
