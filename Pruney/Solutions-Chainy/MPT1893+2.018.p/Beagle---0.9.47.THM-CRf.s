%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:28 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 394 expanded)
%              Number of leaves         :   40 ( 152 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 (1362 expanded)
%              Number of equality atoms :   32 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
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

tff(f_63,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_135,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1037,plain,(
    ! [A_138,B_139] :
      ( k2_pre_topc(A_138,B_139) = B_139
      | ~ v4_pre_topc(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1051,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1037])).

tff(c_1061,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1051])).

tff(c_1063,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1061])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_87,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_99,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_1215,plain,(
    ! [B_158,A_159] :
      ( v4_pre_topc(B_158,A_159)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_159),B_158),A_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1222,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_1215])).

tff(c_1232,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_87,c_1222])).

tff(c_1252,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_1255,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_1252])).

tff(c_1259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1255])).

tff(c_1260,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_1261,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_1412,plain,(
    ! [B_177,A_178] :
      ( v3_pre_topc(B_177,A_178)
      | ~ v4_pre_topc(B_177,A_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ v3_tdlat_3(A_178)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1415,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1261,c_1412])).

tff(c_1436,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_1260,c_1415])).

tff(c_22,plain,(
    ! [B_17,A_15] :
      ( v4_pre_topc(B_17,A_15)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_15),B_17),A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1446,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1436,c_22])).

tff(c_1449,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1446])).

tff(c_1451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1063,c_1449])).

tff(c_1452,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1061])).

tff(c_1458,plain,(
    ! [A_179,B_180] :
      ( k2_pre_topc(A_179,B_180) = u1_struct_0(A_179)
      | ~ v1_tops_1(B_180,A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1472,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1458])).

tff(c_1482,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1452,c_1472])).

tff(c_1484,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_46,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1820,plain,(
    ! [B_214,A_215] :
      ( v1_tops_1(B_214,A_215)
      | ~ v3_tex_2(B_214,A_215)
      | ~ v3_pre_topc(B_214,A_215)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1837,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1820])).

tff(c_1851,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_87,c_46,c_1837])).

tff(c_1853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1484,c_1851])).

tff(c_1854,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_60,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_106,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_103])).

tff(c_206,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,B_62) = B_62
      | ~ v4_pre_topc(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_220,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_206])).

tff(c_230,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_220])).

tff(c_232,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_450,plain,(
    ! [B_90,A_91] :
      ( v4_pre_topc(B_90,A_91)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_91),B_90),A_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_460,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_450])).

tff(c_471,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_87,c_460])).

tff(c_503,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_506,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_503])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_506])).

tff(c_511,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_512,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_32,plain,(
    ! [B_26,A_23] :
      ( v3_pre_topc(B_26,A_23)
      | ~ v4_pre_topc(B_26,A_23)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v3_tdlat_3(A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_541,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_512,c_32])).

tff(c_566,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_511,c_541])).

tff(c_590,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_566,c_22])).

tff(c_593,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_590])).

tff(c_595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_593])).

tff(c_596,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_656,plain,(
    ! [A_103,B_104] :
      ( k2_pre_topc(A_103,B_104) = u1_struct_0(A_103)
      | ~ v1_tops_1(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_670,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_656])).

tff(c_680,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_596,c_670])).

tff(c_682,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_680])).

tff(c_991,plain,(
    ! [B_136,A_137] :
      ( v1_tops_1(B_136,A_137)
      | ~ v3_tex_2(B_136,A_137)
      | ~ v3_pre_topc(B_136,A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1008,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_991])).

tff(c_1022,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_87,c_46,c_1008])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_682,c_1022])).

tff(c_1025,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_680])).

tff(c_44,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_178,plain,(
    ! [A_58,B_59] :
      ( ~ v1_xboole_0(k3_subset_1(A_58,B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58))
      | ~ v1_subset_1(B_59,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_190,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_178])).

tff(c_201,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_190])).

tff(c_205,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_1027,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_205])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_106,c_1027])).

tff(c_1035,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_1857,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_1035])).

tff(c_128,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k3_subset_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    ! [A_7] :
      ( m1_subset_1(A_7,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_128])).

tff(c_147,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_141])).

tff(c_2342,plain,(
    ! [B_252,A_253] :
      ( ~ v3_tex_2(B_252,A_253)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ v1_xboole_0(B_252)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2345,plain,(
    ! [B_252] :
      ( ~ v3_tex_2(B_252,'#skF_2')
      | ~ m1_subset_1(B_252,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0(B_252)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_2342])).

tff(c_2362,plain,(
    ! [B_252] :
      ( ~ v3_tex_2(B_252,'#skF_2')
      | ~ m1_subset_1(B_252,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0(B_252)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2345])).

tff(c_2371,plain,(
    ! [B_255] :
      ( ~ v3_tex_2(B_255,'#skF_2')
      | ~ m1_subset_1(B_255,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0(B_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2362])).

tff(c_2375,plain,
    ( ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_2371])).

tff(c_2387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_46,c_2375])).

tff(c_2389,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2388,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2865,plain,(
    ! [B_315,A_316] :
      ( v3_pre_topc(B_315,A_316)
      | ~ v4_pre_topc(B_315,A_316)
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ v3_tdlat_3(A_316)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2882,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2865])).

tff(c_2895,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_2388,c_2882])).

tff(c_2897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2389,c_2895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:50:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.89  
% 4.52/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.89  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.52/1.89  
% 4.52/1.89  %Foreground sorts:
% 4.52/1.89  
% 4.52/1.89  
% 4.52/1.89  %Background operators:
% 4.52/1.89  
% 4.52/1.89  
% 4.52/1.89  %Foreground operators:
% 4.52/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.52/1.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.52/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.89  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.52/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.52/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.52/1.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.52/1.89  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.52/1.89  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.52/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.89  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.52/1.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.52/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.89  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.52/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.52/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.52/1.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.52/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.52/1.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.52/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.89  
% 4.90/1.91  tff(f_157, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 4.90/1.91  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.90/1.91  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.90/1.91  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.90/1.91  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 4.90/1.92  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.90/1.92  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.90/1.92  tff(f_135, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.90/1.92  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.90/1.92  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.90/1.92  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.90/1.92  tff(f_40, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.90/1.92  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.90/1.92  tff(f_91, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tex_2)).
% 4.90/1.92  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.90/1.92  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_1037, plain, (![A_138, B_139]: (k2_pre_topc(A_138, B_139)=B_139 | ~v4_pre_topc(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.90/1.92  tff(c_1051, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1037])).
% 4.90/1.92  tff(c_1061, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1051])).
% 4.90/1.92  tff(c_1063, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1061])).
% 4.90/1.92  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_54, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.90/1.92  tff(c_48, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_87, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.90/1.92  tff(c_99, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.90/1.92  tff(c_104, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_50, c_99])).
% 4.90/1.92  tff(c_1215, plain, (![B_158, A_159]: (v4_pre_topc(B_158, A_159) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_159), B_158), A_159) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.90/1.92  tff(c_1222, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104, c_1215])).
% 4.90/1.92  tff(c_1232, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_87, c_1222])).
% 4.90/1.92  tff(c_1252, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1232])).
% 4.90/1.92  tff(c_1255, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_1252])).
% 4.90/1.92  tff(c_1259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1255])).
% 4.90/1.92  tff(c_1260, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1232])).
% 4.90/1.92  tff(c_1261, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1232])).
% 4.90/1.92  tff(c_1412, plain, (![B_177, A_178]: (v3_pre_topc(B_177, A_178) | ~v4_pre_topc(B_177, A_178) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_178))) | ~v3_tdlat_3(A_178) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.90/1.92  tff(c_1415, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1261, c_1412])).
% 4.90/1.92  tff(c_1436, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_1260, c_1415])).
% 4.90/1.92  tff(c_22, plain, (![B_17, A_15]: (v4_pre_topc(B_17, A_15) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_15), B_17), A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.90/1.92  tff(c_1446, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1436, c_22])).
% 4.90/1.92  tff(c_1449, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1446])).
% 4.90/1.92  tff(c_1451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1063, c_1449])).
% 4.90/1.92  tff(c_1452, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1061])).
% 4.90/1.92  tff(c_1458, plain, (![A_179, B_180]: (k2_pre_topc(A_179, B_180)=u1_struct_0(A_179) | ~v1_tops_1(B_180, A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.90/1.92  tff(c_1472, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1458])).
% 4.90/1.92  tff(c_1482, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1452, c_1472])).
% 4.90/1.92  tff(c_1484, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1482])).
% 4.90/1.92  tff(c_46, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_1820, plain, (![B_214, A_215]: (v1_tops_1(B_214, A_215) | ~v3_tex_2(B_214, A_215) | ~v3_pre_topc(B_214, A_215) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.90/1.92  tff(c_1837, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1820])).
% 4.90/1.92  tff(c_1851, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_87, c_46, c_1837])).
% 4.90/1.92  tff(c_1853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1484, c_1851])).
% 4.90/1.92  tff(c_1854, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1482])).
% 4.90/1.92  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.90/1.92  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.90/1.92  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.90/1.92  tff(c_12, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.90/1.92  tff(c_59, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 4.90/1.92  tff(c_60, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 4.90/1.92  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.90/1.92  tff(c_103, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_99])).
% 4.90/1.92  tff(c_106, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_103])).
% 4.90/1.92  tff(c_206, plain, (![A_61, B_62]: (k2_pre_topc(A_61, B_62)=B_62 | ~v4_pre_topc(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.90/1.92  tff(c_220, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_206])).
% 4.90/1.92  tff(c_230, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_220])).
% 4.90/1.92  tff(c_232, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_230])).
% 4.90/1.92  tff(c_450, plain, (![B_90, A_91]: (v4_pre_topc(B_90, A_91) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_91), B_90), A_91) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.90/1.92  tff(c_460, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104, c_450])).
% 4.90/1.92  tff(c_471, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_87, c_460])).
% 4.90/1.92  tff(c_503, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_471])).
% 4.90/1.92  tff(c_506, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_503])).
% 4.90/1.92  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_506])).
% 4.90/1.92  tff(c_511, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_471])).
% 4.90/1.92  tff(c_512, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_471])).
% 4.90/1.92  tff(c_32, plain, (![B_26, A_23]: (v3_pre_topc(B_26, A_23) | ~v4_pre_topc(B_26, A_23) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_23))) | ~v3_tdlat_3(A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.90/1.92  tff(c_541, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_512, c_32])).
% 4.90/1.92  tff(c_566, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_511, c_541])).
% 4.90/1.92  tff(c_590, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_566, c_22])).
% 4.90/1.92  tff(c_593, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_590])).
% 4.90/1.92  tff(c_595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_593])).
% 4.90/1.92  tff(c_596, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_230])).
% 4.90/1.92  tff(c_656, plain, (![A_103, B_104]: (k2_pre_topc(A_103, B_104)=u1_struct_0(A_103) | ~v1_tops_1(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.90/1.92  tff(c_670, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_656])).
% 4.90/1.92  tff(c_680, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_596, c_670])).
% 4.90/1.92  tff(c_682, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_680])).
% 4.90/1.92  tff(c_991, plain, (![B_136, A_137]: (v1_tops_1(B_136, A_137) | ~v3_tex_2(B_136, A_137) | ~v3_pre_topc(B_136, A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.90/1.92  tff(c_1008, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_991])).
% 4.90/1.92  tff(c_1022, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_87, c_46, c_1008])).
% 4.90/1.92  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_682, c_1022])).
% 4.90/1.92  tff(c_1025, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_680])).
% 4.90/1.92  tff(c_44, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.90/1.92  tff(c_178, plain, (![A_58, B_59]: (~v1_xboole_0(k3_subset_1(A_58, B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)) | ~v1_subset_1(B_59, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.90/1.92  tff(c_190, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_178])).
% 4.90/1.92  tff(c_201, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_190])).
% 4.90/1.92  tff(c_205, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_201])).
% 4.90/1.92  tff(c_1027, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1025, c_205])).
% 4.90/1.92  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_106, c_1027])).
% 4.90/1.92  tff(c_1035, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_201])).
% 4.90/1.92  tff(c_1857, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_1035])).
% 4.90/1.92  tff(c_128, plain, (![A_49, B_50]: (m1_subset_1(k3_subset_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.90/1.92  tff(c_141, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_128])).
% 4.90/1.92  tff(c_147, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_141])).
% 4.90/1.92  tff(c_2342, plain, (![B_252, A_253]: (~v3_tex_2(B_252, A_253) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_253))) | ~v1_xboole_0(B_252) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.90/1.92  tff(c_2345, plain, (![B_252]: (~v3_tex_2(B_252, '#skF_2') | ~m1_subset_1(B_252, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0(B_252) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_2342])).
% 4.90/1.92  tff(c_2362, plain, (![B_252]: (~v3_tex_2(B_252, '#skF_2') | ~m1_subset_1(B_252, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0(B_252) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2345])).
% 4.90/1.92  tff(c_2371, plain, (![B_255]: (~v3_tex_2(B_255, '#skF_2') | ~m1_subset_1(B_255, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0(B_255))), inference(negUnitSimplification, [status(thm)], [c_58, c_2362])).
% 4.90/1.92  tff(c_2375, plain, (~v3_tex_2('#skF_3', '#skF_2') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_147, c_2371])).
% 4.90/1.92  tff(c_2387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1857, c_46, c_2375])).
% 4.90/1.92  tff(c_2389, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.90/1.92  tff(c_2388, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.90/1.92  tff(c_2865, plain, (![B_315, A_316]: (v3_pre_topc(B_315, A_316) | ~v4_pre_topc(B_315, A_316) | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0(A_316))) | ~v3_tdlat_3(A_316) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.90/1.92  tff(c_2882, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2865])).
% 4.90/1.92  tff(c_2895, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_2388, c_2882])).
% 4.90/1.92  tff(c_2897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2389, c_2895])).
% 4.90/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.92  
% 4.90/1.92  Inference rules
% 4.90/1.92  ----------------------
% 4.90/1.92  #Ref     : 0
% 4.90/1.92  #Sup     : 540
% 4.90/1.92  #Fact    : 0
% 4.90/1.92  #Define  : 0
% 4.90/1.92  #Split   : 21
% 4.90/1.92  #Chain   : 0
% 4.90/1.92  #Close   : 0
% 4.90/1.92  
% 4.90/1.92  Ordering : KBO
% 4.90/1.92  
% 4.90/1.92  Simplification rules
% 4.90/1.92  ----------------------
% 4.90/1.92  #Subsume      : 46
% 4.90/1.92  #Demod        : 440
% 4.90/1.92  #Tautology    : 210
% 4.90/1.92  #SimpNegUnit  : 35
% 4.90/1.92  #BackRed      : 11
% 4.90/1.92  
% 4.90/1.92  #Partial instantiations: 0
% 4.90/1.92  #Strategies tried      : 1
% 4.90/1.92  
% 4.90/1.92  Timing (in seconds)
% 4.90/1.92  ----------------------
% 4.90/1.92  Preprocessing        : 0.35
% 4.90/1.92  Parsing              : 0.20
% 4.90/1.92  CNF conversion       : 0.02
% 4.90/1.92  Main loop            : 0.74
% 4.90/1.92  Inferencing          : 0.29
% 4.90/1.92  Reduction            : 0.24
% 4.90/1.92  Demodulation         : 0.16
% 4.90/1.92  BG Simplification    : 0.03
% 4.90/1.92  Subsumption          : 0.11
% 4.90/1.92  Abstraction          : 0.03
% 4.90/1.92  MUC search           : 0.00
% 4.90/1.92  Cooper               : 0.00
% 4.90/1.92  Total                : 1.14
% 4.90/1.92  Index Insertion      : 0.00
% 4.90/1.92  Index Deletion       : 0.00
% 4.90/1.92  Index Matching       : 0.00
% 4.90/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
