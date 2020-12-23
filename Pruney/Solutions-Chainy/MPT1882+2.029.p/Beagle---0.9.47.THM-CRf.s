%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:16 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 418 expanded)
%              Number of leaves         :   35 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  245 (1505 expanded)
%              Number of equality atoms :   24 (  94 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > o_1_1_filter_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(o_1_1_filter_1,type,(
    o_1_1_filter_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => m1_subset_1(o_1_1_filter_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_1_filter_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_97,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_20,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_14] :
      ( m1_subset_1(o_1_1_filter_1(A_14),A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_102,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_109,plain,(
    ! [B_47] :
      ( r1_tarski(o_1_1_filter_1(k1_zfmisc_1(B_47)),B_47)
      | v1_xboole_0(k1_zfmisc_1(B_47)) ) ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_118,plain,(
    ! [B_48] : r1_tarski(o_1_1_filter_1(k1_zfmisc_1(B_48)),B_48) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_109])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    o_1_1_filter_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_14])).

tff(c_116,plain,(
    ! [B_47] : r1_tarski(o_1_1_filter_1(k1_zfmisc_1(B_47)),B_47) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_109])).

tff(c_12,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_154,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,k2_xboole_0(C_52,B_53))
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_161,plain,(
    ! [A_54,A_55] :
      ( r1_tarski(A_54,A_55)
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_154])).

tff(c_164,plain,(
    ! [A_55] : r1_tarski(o_1_1_filter_1(k1_zfmisc_1(k1_xboole_0)),A_55) ),
    inference(resolution,[status(thm)],[c_116,c_161])).

tff(c_169,plain,(
    ! [A_55] : r1_tarski(k1_xboole_0,A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_164])).

tff(c_66,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_80,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_89,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_60])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_zfmisc_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_396,plain,(
    ! [A_79,B_80] :
      ( '#skF_1'(A_79,B_80) != B_80
      | v3_tex_2(B_80,A_79)
      | ~ v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_411,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_396])).

tff(c_419,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_411])).

tff(c_420,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_419])).

tff(c_421,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_889,plain,(
    ! [B_102,A_103] :
      ( v2_tex_2(B_102,A_103)
      | ~ v1_zfmisc_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | v1_xboole_0(B_102)
      | ~ l1_pre_topc(A_103)
      | ~ v2_tdlat_3(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_923,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_889])).

tff(c_938,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_80,c_923])).

tff(c_940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_421,c_938])).

tff(c_941,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_942,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_1223,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(B_112,'#skF_1'(A_113,B_112))
      | v3_tex_2(B_112,A_113)
      | ~ v2_tex_2(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1237,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1223])).

tff(c_1247,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_942,c_1237])).

tff(c_1248,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1247])).

tff(c_40,plain,(
    ! [B_27,A_25] :
      ( B_27 = A_25
      | ~ r1_tarski(A_25,B_27)
      | ~ v1_zfmisc_1(B_27)
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1253,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1248,c_40])).

tff(c_1261,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_941,c_1253])).

tff(c_1265,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1261])).

tff(c_1269,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_1265])).

tff(c_1110,plain,(
    ! [A_108,B_109] :
      ( v2_tex_2('#skF_1'(A_108,B_109),A_108)
      | v3_tex_2(B_109,A_108)
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1121,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1110])).

tff(c_1129,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_942,c_1121])).

tff(c_1130,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1129])).

tff(c_1476,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1('#skF_1'(A_124,B_125),k1_zfmisc_1(u1_struct_0(A_124)))
      | v3_tex_2(B_125,A_124)
      | ~ v2_tex_2(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [B_33,A_31] :
      ( v1_zfmisc_1(B_33)
      | ~ v2_tex_2(B_33,A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | v1_xboole_0(B_33)
      | ~ l1_pre_topc(A_31)
      | ~ v2_tdlat_3(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5884,plain,(
    ! [A_256,B_257] :
      ( v1_zfmisc_1('#skF_1'(A_256,B_257))
      | ~ v2_tex_2('#skF_1'(A_256,B_257),A_256)
      | v1_xboole_0('#skF_1'(A_256,B_257))
      | ~ v2_tdlat_3(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256)
      | v3_tex_2(B_257,A_256)
      | ~ v2_tex_2(B_257,A_256)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(resolution,[status(thm)],[c_1476,c_46])).

tff(c_5898,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1130,c_5884])).

tff(c_5910,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_942,c_56,c_54,c_5898])).

tff(c_5912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_58,c_1269,c_1265,c_5910])).

tff(c_5913,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1261])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_90,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_93,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_5920,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5913,c_93])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_249,plain,(
    ! [C_62,B_63,A_64] :
      ( k2_xboole_0(C_62,B_63) = A_64
      | ~ r1_tarski(k2_xboole_0(C_62,B_63),A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_256,plain,(
    ! [A_6,A_64] :
      ( k2_xboole_0(A_6,k1_xboole_0) = A_64
      | ~ r1_tarski(A_6,A_64)
      | ~ r1_tarski(A_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_249])).

tff(c_262,plain,(
    ! [A_64,A_6] :
      ( A_64 = A_6
      | ~ r1_tarski(A_6,A_64)
      | ~ r1_tarski(A_64,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_256])).

tff(c_1250,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1248,c_262])).

tff(c_1258,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_941,c_1250])).

tff(c_5924,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5920,c_1258])).

tff(c_5932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_5924])).

tff(c_5934,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5933,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6096,plain,(
    ! [B_279,A_280] :
      ( v2_tex_2(B_279,A_280)
      | ~ v3_tex_2(B_279,A_280)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6107,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_6096])).

tff(c_6114,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5933,c_6107])).

tff(c_6749,plain,(
    ! [B_318,A_319] :
      ( v1_zfmisc_1(B_318)
      | ~ v2_tex_2(B_318,A_319)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_319)))
      | v1_xboole_0(B_318)
      | ~ l1_pre_topc(A_319)
      | ~ v2_tdlat_3(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6780,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_6749])).

tff(c_6794,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_6114,c_6780])).

tff(c_6796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_5934,c_6794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.19/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.78  
% 8.19/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.79  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > o_1_1_filter_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.19/2.79  
% 8.19/2.79  %Foreground sorts:
% 8.19/2.79  
% 8.19/2.79  
% 8.19/2.79  %Background operators:
% 8.19/2.79  
% 8.19/2.79  
% 8.19/2.79  %Foreground operators:
% 8.19/2.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.19/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.19/2.79  tff(o_1_1_filter_1, type, o_1_1_filter_1: $i > $i).
% 8.19/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.19/2.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.19/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.19/2.79  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 8.19/2.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.19/2.79  tff('#skF_2', type, '#skF_2': $i).
% 8.19/2.79  tff('#skF_3', type, '#skF_3': $i).
% 8.19/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.19/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.19/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.19/2.79  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.19/2.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.19/2.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.19/2.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.19/2.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.19/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.19/2.79  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.19/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.19/2.79  
% 8.19/2.80  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 8.19/2.80  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.19/2.80  tff(f_66, axiom, (![A]: (~v1_xboole_0(A) => m1_subset_1(o_1_1_filter_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_1_1_filter_1)).
% 8.19/2.80  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.19/2.80  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.19/2.80  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 8.19/2.80  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.19/2.80  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 8.19/2.80  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 8.19/2.80  tff(f_130, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 8.19/2.80  tff(f_97, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 8.19/2.80  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.19/2.80  tff(f_50, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.19/2.80  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.19/2.80  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_20, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.19/2.80  tff(c_26, plain, (![A_14]: (m1_subset_1(o_1_1_filter_1(A_14), A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.19/2.80  tff(c_102, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.19/2.80  tff(c_109, plain, (![B_47]: (r1_tarski(o_1_1_filter_1(k1_zfmisc_1(B_47)), B_47) | v1_xboole_0(k1_zfmisc_1(B_47)))), inference(resolution, [status(thm)], [c_26, c_102])).
% 8.19/2.80  tff(c_118, plain, (![B_48]: (r1_tarski(o_1_1_filter_1(k1_zfmisc_1(B_48)), B_48))), inference(negUnitSimplification, [status(thm)], [c_20, c_109])).
% 8.19/2.80  tff(c_14, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.19/2.80  tff(c_123, plain, (o_1_1_filter_1(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_118, c_14])).
% 8.19/2.80  tff(c_116, plain, (![B_47]: (r1_tarski(o_1_1_filter_1(k1_zfmisc_1(B_47)), B_47))), inference(negUnitSimplification, [status(thm)], [c_20, c_109])).
% 8.19/2.80  tff(c_12, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.19/2.80  tff(c_154, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, k2_xboole_0(C_52, B_53)) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.19/2.80  tff(c_161, plain, (![A_54, A_55]: (r1_tarski(A_54, A_55) | ~r1_tarski(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_154])).
% 8.19/2.80  tff(c_164, plain, (![A_55]: (r1_tarski(o_1_1_filter_1(k1_zfmisc_1(k1_xboole_0)), A_55))), inference(resolution, [status(thm)], [c_116, c_161])).
% 8.19/2.80  tff(c_169, plain, (![A_55]: (r1_tarski(k1_xboole_0, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_164])).
% 8.19/2.80  tff(c_66, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_80, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 8.19/2.80  tff(c_60, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_89, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_60])).
% 8.19/2.80  tff(c_18, plain, (![A_10]: (v1_zfmisc_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.19/2.80  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_396, plain, (![A_79, B_80]: ('#skF_1'(A_79, B_80)!=B_80 | v3_tex_2(B_80, A_79) | ~v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.19/2.80  tff(c_411, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_396])).
% 8.19/2.80  tff(c_419, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_411])).
% 8.19/2.80  tff(c_420, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_89, c_419])).
% 8.19/2.80  tff(c_421, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_420])).
% 8.19/2.80  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_54, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.19/2.80  tff(c_889, plain, (![B_102, A_103]: (v2_tex_2(B_102, A_103) | ~v1_zfmisc_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | v1_xboole_0(B_102) | ~l1_pre_topc(A_103) | ~v2_tdlat_3(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.19/2.80  tff(c_923, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_889])).
% 8.19/2.80  tff(c_938, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_80, c_923])).
% 8.19/2.80  tff(c_940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_421, c_938])).
% 8.19/2.80  tff(c_941, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_420])).
% 8.19/2.80  tff(c_942, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_420])).
% 8.19/2.80  tff(c_1223, plain, (![B_112, A_113]: (r1_tarski(B_112, '#skF_1'(A_113, B_112)) | v3_tex_2(B_112, A_113) | ~v2_tex_2(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.19/2.80  tff(c_1237, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1223])).
% 8.19/2.80  tff(c_1247, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_942, c_1237])).
% 8.19/2.80  tff(c_1248, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_89, c_1247])).
% 8.19/2.80  tff(c_40, plain, (![B_27, A_25]: (B_27=A_25 | ~r1_tarski(A_25, B_27) | ~v1_zfmisc_1(B_27) | v1_xboole_0(B_27) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.19/2.80  tff(c_1253, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1248, c_40])).
% 8.19/2.80  tff(c_1261, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_941, c_1253])).
% 8.19/2.80  tff(c_1265, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1261])).
% 8.19/2.80  tff(c_1269, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1265])).
% 8.19/2.80  tff(c_1110, plain, (![A_108, B_109]: (v2_tex_2('#skF_1'(A_108, B_109), A_108) | v3_tex_2(B_109, A_108) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.19/2.80  tff(c_1121, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1110])).
% 8.19/2.80  tff(c_1129, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_942, c_1121])).
% 8.19/2.80  tff(c_1130, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_89, c_1129])).
% 8.19/2.80  tff(c_1476, plain, (![A_124, B_125]: (m1_subset_1('#skF_1'(A_124, B_125), k1_zfmisc_1(u1_struct_0(A_124))) | v3_tex_2(B_125, A_124) | ~v2_tex_2(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.19/2.80  tff(c_46, plain, (![B_33, A_31]: (v1_zfmisc_1(B_33) | ~v2_tex_2(B_33, A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | v1_xboole_0(B_33) | ~l1_pre_topc(A_31) | ~v2_tdlat_3(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.19/2.80  tff(c_5884, plain, (![A_256, B_257]: (v1_zfmisc_1('#skF_1'(A_256, B_257)) | ~v2_tex_2('#skF_1'(A_256, B_257), A_256) | v1_xboole_0('#skF_1'(A_256, B_257)) | ~v2_tdlat_3(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256) | v3_tex_2(B_257, A_256) | ~v2_tex_2(B_257, A_256) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(resolution, [status(thm)], [c_1476, c_46])).
% 8.19/2.80  tff(c_5898, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1130, c_5884])).
% 8.19/2.80  tff(c_5910, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_942, c_56, c_54, c_5898])).
% 8.19/2.80  tff(c_5912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_58, c_1269, c_1265, c_5910])).
% 8.19/2.80  tff(c_5913, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1261])).
% 8.19/2.80  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.19/2.80  tff(c_90, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.19/2.80  tff(c_93, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_2, c_90])).
% 8.19/2.80  tff(c_5920, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5913, c_93])).
% 8.19/2.80  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.19/2.80  tff(c_249, plain, (![C_62, B_63, A_64]: (k2_xboole_0(C_62, B_63)=A_64 | ~r1_tarski(k2_xboole_0(C_62, B_63), A_64) | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_154, c_4])).
% 8.19/2.80  tff(c_256, plain, (![A_6, A_64]: (k2_xboole_0(A_6, k1_xboole_0)=A_64 | ~r1_tarski(A_6, A_64) | ~r1_tarski(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_249])).
% 8.19/2.80  tff(c_262, plain, (![A_64, A_6]: (A_64=A_6 | ~r1_tarski(A_6, A_64) | ~r1_tarski(A_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_256])).
% 8.19/2.80  tff(c_1250, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_1248, c_262])).
% 8.19/2.80  tff(c_1258, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_941, c_1250])).
% 8.19/2.80  tff(c_5924, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5920, c_1258])).
% 8.19/2.80  tff(c_5932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_5924])).
% 8.19/2.80  tff(c_5934, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 8.19/2.80  tff(c_5933, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 8.19/2.80  tff(c_6096, plain, (![B_279, A_280]: (v2_tex_2(B_279, A_280) | ~v3_tex_2(B_279, A_280) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.19/2.80  tff(c_6107, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_6096])).
% 8.19/2.80  tff(c_6114, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5933, c_6107])).
% 8.19/2.80  tff(c_6749, plain, (![B_318, A_319]: (v1_zfmisc_1(B_318) | ~v2_tex_2(B_318, A_319) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_319))) | v1_xboole_0(B_318) | ~l1_pre_topc(A_319) | ~v2_tdlat_3(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.19/2.80  tff(c_6780, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_6749])).
% 8.19/2.80  tff(c_6794, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_6114, c_6780])).
% 8.19/2.80  tff(c_6796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_5934, c_6794])).
% 8.19/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.19/2.80  
% 8.19/2.80  Inference rules
% 8.19/2.80  ----------------------
% 8.19/2.80  #Ref     : 5
% 8.19/2.80  #Sup     : 1593
% 8.19/2.80  #Fact    : 18
% 8.19/2.80  #Define  : 0
% 8.19/2.80  #Split   : 15
% 8.19/2.80  #Chain   : 0
% 8.19/2.80  #Close   : 0
% 8.19/2.80  
% 8.19/2.80  Ordering : KBO
% 8.19/2.80  
% 8.19/2.80  Simplification rules
% 8.19/2.80  ----------------------
% 8.19/2.80  #Subsume      : 768
% 8.19/2.80  #Demod        : 432
% 8.19/2.80  #Tautology    : 297
% 8.19/2.80  #SimpNegUnit  : 111
% 8.19/2.80  #BackRed      : 7
% 8.19/2.80  
% 8.19/2.80  #Partial instantiations: 0
% 8.19/2.80  #Strategies tried      : 1
% 8.19/2.80  
% 8.19/2.80  Timing (in seconds)
% 8.19/2.80  ----------------------
% 8.34/2.81  Preprocessing        : 0.33
% 8.34/2.81  Parsing              : 0.18
% 8.34/2.81  CNF conversion       : 0.02
% 8.34/2.81  Main loop            : 1.68
% 8.34/2.81  Inferencing          : 0.45
% 8.34/2.81  Reduction            : 0.44
% 8.34/2.81  Demodulation         : 0.28
% 8.34/2.81  BG Simplification    : 0.05
% 8.34/2.81  Subsumption          : 0.65
% 8.34/2.81  Abstraction          : 0.08
% 8.34/2.81  MUC search           : 0.00
% 8.34/2.81  Cooper               : 0.00
% 8.34/2.81  Total                : 2.04
% 8.34/2.81  Index Insertion      : 0.00
% 8.34/2.81  Index Deletion       : 0.00
% 8.34/2.81  Index Matching       : 0.00
% 8.34/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
