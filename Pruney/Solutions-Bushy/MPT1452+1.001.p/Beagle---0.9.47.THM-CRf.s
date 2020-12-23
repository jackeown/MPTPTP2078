%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1452+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:56 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 781 expanded)
%              Number of leaves         :   42 ( 291 expanded)
%              Depth                    :   10
%              Number of atoms          :  615 (5323 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v3_lattices > v3_filter_0 > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > k6_filter_1 > g3_lattices > k7_filter_1 > k2_zfmisc_1 > #nlpp > u2_lattices > u1_struct_0 > u1_lattices > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(u2_lattices,type,(
    u2_lattices: $i > $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_filter_1,type,(
    k6_filter_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_lattices,type,(
    u1_lattices: $i > $i )).

tff(g3_lattices,type,(
    g3_lattices: ( $i * $i * $i ) > $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

tff(k7_filter_1,type,(
    k7_filter_1: ( $i * $i ) > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v16_lattices,type,(
    v16_lattices: $i > $o )).

tff(v3_filter_0,type,(
    v3_filter_0: $i > $o )).

tff(v15_lattices,type,(
    v15_lattices: $i > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_340,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v10_lattices(B)
              & l3_lattices(B) )
           => ( ( ~ v2_struct_0(A)
                & v10_lattices(A)
                & v17_lattices(A)
                & l3_lattices(A)
                & ~ v2_struct_0(B)
                & v10_lattices(B)
                & v17_lattices(B)
                & l3_lattices(B) )
            <=> ( ~ v2_struct_0(k7_filter_1(A,B))
                & v10_lattices(k7_filter_1(A,B))
                & v17_lattices(k7_filter_1(A,B))
                & l3_lattices(k7_filter_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_filter_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & v10_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_filter_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

tff(f_56,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v17_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_lattices)).

tff(f_249,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v11_lattices(A)
              & l3_lattices(A)
              & ~ v2_struct_0(B)
              & v10_lattices(B)
              & v11_lattices(B)
              & l3_lattices(B) )
          <=> ( ~ v2_struct_0(k7_filter_1(A,B))
              & v10_lattices(k7_filter_1(A,B))
              & v11_lattices(k7_filter_1(A,B))
              & l3_lattices(k7_filter_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_filter_1)).

tff(f_297,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v15_lattices(A)
              & v16_lattices(A)
              & l3_lattices(A)
              & ~ v2_struct_0(B)
              & v10_lattices(B)
              & v15_lattices(B)
              & v16_lattices(B)
              & l3_lattices(B) )
          <=> ( ~ v2_struct_0(k7_filter_1(A,B))
              & v10_lattices(k7_filter_1(A,B))
              & v15_lattices(k7_filter_1(A,B))
              & v16_lattices(k7_filter_1(A,B))
              & l3_lattices(k7_filter_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_filter_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( ~ v2_struct_0(k7_filter_1(A,B))
        & v3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_filter_1)).

tff(c_178,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_172,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_174,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_168,plain,(
    l3_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_2796,plain,(
    ! [A_322,B_323] :
      ( l3_lattices(k7_filter_1(A_322,B_323))
      | ~ l3_lattices(B_323)
      | v2_struct_0(B_323)
      | ~ l3_lattices(A_322)
      | v2_struct_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_176,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_170,plain,(
    v10_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_2569,plain,(
    ! [A_316,B_317] :
      ( v10_lattices(k7_filter_1(A_316,B_317))
      | ~ l3_lattices(B_317)
      | ~ v10_lattices(B_317)
      | v2_struct_0(B_317)
      | ~ l3_lattices(A_316)
      | ~ v10_lattices(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_264,plain,
    ( v17_lattices('#skF_8')
    | ~ v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_299,plain,(
    ~ v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_302,plain,(
    ! [A_19] :
      ( v16_lattices(A_19)
      | ~ v17_lattices(A_19)
      | v2_struct_0(A_19)
      | ~ l3_lattices(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_326,plain,
    ( v16_lattices('#skF_8')
    | ~ v17_lattices('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_302,c_178])).

tff(c_350,plain,
    ( v16_lattices('#skF_8')
    | ~ v17_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_326])).

tff(c_401,plain,(
    ~ v17_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_455,plain,(
    ! [A_22] :
      ( v17_lattices(A_22)
      | ~ v16_lattices(A_22)
      | ~ v15_lattices(A_22)
      | ~ v11_lattices(A_22)
      | v2_struct_0(A_22)
      | ~ l3_lattices(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_479,plain,
    ( v17_lattices('#skF_8')
    | ~ v16_lattices('#skF_8')
    | ~ v15_lattices('#skF_8')
    | ~ v11_lattices('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_455,c_178])).

tff(c_508,plain,
    ( v17_lattices('#skF_8')
    | ~ v16_lattices('#skF_8')
    | ~ v15_lattices('#skF_8')
    | ~ v11_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_479])).

tff(c_509,plain,
    ( ~ v16_lattices('#skF_8')
    | ~ v15_lattices('#skF_8')
    | ~ v11_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_508])).

tff(c_511,plain,(
    ~ v11_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_238,plain,
    ( v17_lattices('#skF_9')
    | v10_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_296,plain,(
    v10_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_202,plain,
    ( v17_lattices('#skF_9')
    | l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_295,plain,(
    l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_228,plain,
    ( v17_lattices('#skF_8')
    | v17_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_297,plain,(
    v17_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_405,plain,(
    ! [A_21] :
      ( v11_lattices(A_21)
      | ~ v17_lattices(A_21)
      | v2_struct_0(A_21)
      | ~ l3_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_408,plain,
    ( v11_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_405,c_299])).

tff(c_432,plain,(
    v11_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_297,c_408])).

tff(c_579,plain,(
    ! [A_45,B_46] :
      ( v11_lattices(A_45)
      | ~ l3_lattices(k7_filter_1(A_45,B_46))
      | ~ v11_lattices(k7_filter_1(A_45,B_46))
      | ~ v10_lattices(k7_filter_1(A_45,B_46))
      | v2_struct_0(k7_filter_1(A_45,B_46))
      | ~ l3_lattices(B_46)
      | ~ v10_lattices(B_46)
      | v2_struct_0(B_46)
      | ~ l3_lattices(A_45)
      | ~ v10_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_585,plain,
    ( v11_lattices('#skF_8')
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v11_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_579,c_299])).

tff(c_589,plain,
    ( v11_lattices('#skF_8')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_296,c_432,c_295,c_585])).

tff(c_591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_511,c_589])).

tff(c_592,plain,
    ( ~ v15_lattices('#skF_8')
    | ~ v16_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_595,plain,(
    ~ v16_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_352,plain,(
    ! [A_20] :
      ( v15_lattices(A_20)
      | ~ v17_lattices(A_20)
      | v2_struct_0(A_20)
      | ~ l3_lattices(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_355,plain,
    ( v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_352,c_299])).

tff(c_379,plain,(
    v15_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_297,c_355])).

tff(c_305,plain,
    ( v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_302,c_299])).

tff(c_329,plain,(
    v16_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_297,c_305])).

tff(c_826,plain,(
    ! [A_105,B_106] :
      ( v16_lattices(A_105)
      | ~ l3_lattices(k7_filter_1(A_105,B_106))
      | ~ v16_lattices(k7_filter_1(A_105,B_106))
      | ~ v15_lattices(k7_filter_1(A_105,B_106))
      | ~ v10_lattices(k7_filter_1(A_105,B_106))
      | v2_struct_0(k7_filter_1(A_105,B_106))
      | ~ l3_lattices(B_106)
      | ~ v10_lattices(B_106)
      | v2_struct_0(B_106)
      | ~ l3_lattices(A_105)
      | ~ v10_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_832,plain,
    ( v16_lattices('#skF_8')
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_826,c_299])).

tff(c_836,plain,
    ( v16_lattices('#skF_8')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_296,c_379,c_329,c_295,c_832])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_595,c_836])).

tff(c_839,plain,(
    ~ v15_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_1059,plain,(
    ! [A_161,B_162] :
      ( v15_lattices(A_161)
      | ~ l3_lattices(k7_filter_1(A_161,B_162))
      | ~ v16_lattices(k7_filter_1(A_161,B_162))
      | ~ v15_lattices(k7_filter_1(A_161,B_162))
      | ~ v10_lattices(k7_filter_1(A_161,B_162))
      | v2_struct_0(k7_filter_1(A_161,B_162))
      | ~ l3_lattices(B_162)
      | ~ v10_lattices(B_162)
      | v2_struct_0(B_162)
      | ~ l3_lattices(A_161)
      | ~ v10_lattices(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_1065,plain,
    ( v15_lattices('#skF_8')
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1059,c_299])).

tff(c_1069,plain,
    ( v15_lattices('#skF_8')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_296,c_379,c_329,c_295,c_1065])).

tff(c_1071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_839,c_1069])).

tff(c_1073,plain,(
    v17_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_1074,plain,(
    ! [A_163] :
      ( v11_lattices(A_163)
      | ~ v17_lattices(A_163)
      | v2_struct_0(A_163)
      | ~ l3_lattices(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1095,plain,
    ( v11_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_1074,c_172])).

tff(c_1119,plain,
    ( v11_lattices('#skF_9')
    | ~ v17_lattices('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1095])).

tff(c_1124,plain,(
    ~ v17_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1119])).

tff(c_1132,plain,(
    ! [A_166] :
      ( v17_lattices(A_166)
      | ~ v16_lattices(A_166)
      | ~ v15_lattices(A_166)
      | ~ v11_lattices(A_166)
      | v2_struct_0(A_166)
      | ~ l3_lattices(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1153,plain,
    ( v17_lattices('#skF_9')
    | ~ v16_lattices('#skF_9')
    | ~ v15_lattices('#skF_9')
    | ~ v11_lattices('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_1132,c_172])).

tff(c_1181,plain,
    ( v17_lattices('#skF_9')
    | ~ v16_lattices('#skF_9')
    | ~ v15_lattices('#skF_9')
    | ~ v11_lattices('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1153])).

tff(c_1182,plain,
    ( ~ v16_lattices('#skF_9')
    | ~ v15_lattices('#skF_9')
    | ~ v11_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1124,c_1181])).

tff(c_1206,plain,(
    ~ v11_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1182])).

tff(c_1077,plain,
    ( v11_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_1074,c_299])).

tff(c_1101,plain,(
    v11_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_297,c_1077])).

tff(c_1253,plain,(
    ! [B_187,A_188] :
      ( v11_lattices(B_187)
      | ~ l3_lattices(k7_filter_1(A_188,B_187))
      | ~ v11_lattices(k7_filter_1(A_188,B_187))
      | ~ v10_lattices(k7_filter_1(A_188,B_187))
      | v2_struct_0(k7_filter_1(A_188,B_187))
      | ~ l3_lattices(B_187)
      | ~ v10_lattices(B_187)
      | v2_struct_0(B_187)
      | ~ l3_lattices(A_188)
      | ~ v10_lattices(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_1259,plain,
    ( v11_lattices('#skF_9')
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v11_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1253,c_299])).

tff(c_1263,plain,
    ( v11_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_296,c_1101,c_295,c_1259])).

tff(c_1265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_1206,c_1263])).

tff(c_1266,plain,
    ( ~ v15_lattices('#skF_9')
    | ~ v16_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1182])).

tff(c_1268,plain,(
    ~ v16_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_1363,plain,(
    ! [B_215,A_216] :
      ( v16_lattices(B_215)
      | ~ l3_lattices(k7_filter_1(A_216,B_215))
      | ~ v16_lattices(k7_filter_1(A_216,B_215))
      | ~ v15_lattices(k7_filter_1(A_216,B_215))
      | ~ v10_lattices(k7_filter_1(A_216,B_215))
      | v2_struct_0(k7_filter_1(A_216,B_215))
      | ~ l3_lattices(B_215)
      | ~ v10_lattices(B_215)
      | v2_struct_0(B_215)
      | ~ l3_lattices(A_216)
      | ~ v10_lattices(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_1369,plain,
    ( v16_lattices('#skF_9')
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1363,c_299])).

tff(c_1373,plain,
    ( v16_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_296,c_379,c_329,c_295,c_1369])).

tff(c_1375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_1268,c_1373])).

tff(c_1376,plain,(
    ~ v15_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_1520,plain,(
    ! [B_251,A_252] :
      ( v15_lattices(B_251)
      | ~ l3_lattices(k7_filter_1(A_252,B_251))
      | ~ v16_lattices(k7_filter_1(A_252,B_251))
      | ~ v15_lattices(k7_filter_1(A_252,B_251))
      | ~ v10_lattices(k7_filter_1(A_252,B_251))
      | v2_struct_0(k7_filter_1(A_252,B_251))
      | ~ l3_lattices(B_251)
      | ~ v10_lattices(B_251)
      | v2_struct_0(B_251)
      | ~ l3_lattices(A_252)
      | ~ v10_lattices(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_1526,plain,
    ( v15_lattices('#skF_9')
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1520,c_299])).

tff(c_1530,plain,
    ( v15_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_296,c_379,c_329,c_295,c_1526])).

tff(c_1532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_1376,c_1530])).

tff(c_1534,plain,(
    v17_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1119])).

tff(c_180,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v17_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_269,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v17_lattices('#skF_8')
    | ~ v10_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_180])).

tff(c_275,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v17_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_269])).

tff(c_281,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ v17_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_275])).

tff(c_282,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | ~ v17_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_281])).

tff(c_288,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ v17_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_282])).

tff(c_294,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v10_lattices(k7_filter_1('#skF_8','#skF_9'))
    | v2_struct_0(k7_filter_1('#skF_8','#skF_9'))
    | ~ v17_lattices('#skF_9')
    | ~ v17_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_288])).

tff(c_1618,plain,(
    v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_1534,c_296,c_297,c_295,c_294])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_1618])).

tff(c_1621,plain,(
    v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_1813,plain,(
    ! [A_266,B_267] :
      ( ~ v2_struct_0(k7_filter_1(A_266,B_267))
      | ~ l3_lattices(B_267)
      | v2_struct_0(B_267)
      | ~ l3_lattices(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1828,plain,
    ( ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1621,c_1813])).

tff(c_1835,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_168,c_1828])).

tff(c_1837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_1835])).

tff(c_1838,plain,(
    v17_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_1947,plain,(
    ! [A_270] :
      ( v15_lattices(A_270)
      | ~ v17_lattices(A_270)
      | v2_struct_0(A_270)
      | ~ l3_lattices(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1971,plain,
    ( v15_lattices('#skF_8')
    | ~ v17_lattices('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_1947,c_178])).

tff(c_1995,plain,(
    v15_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_1838,c_1971])).

tff(c_1896,plain,(
    ! [A_269] :
      ( v16_lattices(A_269)
      | ~ v17_lattices(A_269)
      | v2_struct_0(A_269)
      | ~ l3_lattices(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1920,plain,
    ( v16_lattices('#skF_8')
    | ~ v17_lattices('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_1896,c_178])).

tff(c_1944,plain,(
    v16_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_1838,c_1920])).

tff(c_1839,plain,(
    ~ v17_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_220,plain,
    ( v17_lattices('#skF_9')
    | v17_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_1844,plain,(
    v17_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1839,c_220])).

tff(c_1968,plain,
    ( v15_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_1947,c_172])).

tff(c_1992,plain,(
    v15_lattices('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1844,c_1968])).

tff(c_1917,plain,
    ( v16_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_1896,c_172])).

tff(c_1941,plain,(
    v16_lattices('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1844,c_1917])).

tff(c_2109,plain,(
    ! [A_296,B_297] :
      ( v15_lattices(k7_filter_1(A_296,B_297))
      | ~ v16_lattices(B_297)
      | ~ v15_lattices(B_297)
      | ~ v16_lattices(A_296)
      | ~ v15_lattices(A_296)
      | ~ l3_lattices(B_297)
      | ~ v10_lattices(B_297)
      | v2_struct_0(B_297)
      | ~ l3_lattices(A_296)
      | ~ v10_lattices(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_2095,plain,(
    ! [A_288,B_289] :
      ( v16_lattices(k7_filter_1(A_288,B_289))
      | ~ v16_lattices(B_289)
      | ~ v15_lattices(B_289)
      | ~ v16_lattices(A_288)
      | ~ v15_lattices(A_288)
      | ~ l3_lattices(B_289)
      | ~ v10_lattices(B_289)
      | v2_struct_0(B_289)
      | ~ l3_lattices(A_288)
      | ~ v10_lattices(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_1845,plain,(
    ! [A_268] :
      ( v11_lattices(A_268)
      | ~ v17_lattices(A_268)
      | v2_struct_0(A_268)
      | ~ l3_lattices(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1869,plain,
    ( v11_lattices('#skF_8')
    | ~ v17_lattices('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_1845,c_178])).

tff(c_1893,plain,(
    v11_lattices('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_1838,c_1869])).

tff(c_1866,plain,
    ( v11_lattices('#skF_9')
    | ~ v17_lattices('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_1845,c_172])).

tff(c_1890,plain,(
    v11_lattices('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1844,c_1866])).

tff(c_2078,plain,(
    ! [A_280,B_281] :
      ( v11_lattices(k7_filter_1(A_280,B_281))
      | ~ v11_lattices(B_281)
      | ~ v11_lattices(A_280)
      | ~ l3_lattices(B_281)
      | ~ v10_lattices(B_281)
      | v2_struct_0(B_281)
      | ~ l3_lattices(A_280)
      | ~ v10_lattices(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_2014,plain,(
    ! [A_277] :
      ( v17_lattices(A_277)
      | ~ v16_lattices(A_277)
      | ~ v15_lattices(A_277)
      | ~ v11_lattices(A_277)
      | v2_struct_0(A_277)
      | ~ l3_lattices(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_256,plain,
    ( v17_lattices('#skF_9')
    | ~ v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_340])).

tff(c_1841,plain,(
    ~ v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_2020,plain,
    ( v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v11_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_2014,c_1841])).

tff(c_2045,plain,
    ( v17_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v11_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_2020])).

tff(c_2046,plain,
    ( ~ v16_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v11_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1839,c_2045])).

tff(c_2074,plain,(
    ~ v11_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2046])).

tff(c_2081,plain,
    ( ~ v11_lattices('#skF_9')
    | ~ v11_lattices('#skF_8')
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2078,c_2074])).

tff(c_2084,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_1893,c_1890,c_2081])).

tff(c_2086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_2084])).

tff(c_2087,plain,
    ( ~ v15_lattices(k7_filter_1('#skF_8','#skF_9'))
    | ~ v16_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2046])).

tff(c_2091,plain,(
    ~ v16_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2087])).

tff(c_2098,plain,
    ( ~ v16_lattices('#skF_9')
    | ~ v15_lattices('#skF_9')
    | ~ v16_lattices('#skF_8')
    | ~ v15_lattices('#skF_8')
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2095,c_2091])).

tff(c_2101,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_1995,c_1944,c_1992,c_1941,c_2098])).

tff(c_2103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_2101])).

tff(c_2104,plain,(
    ~ v15_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2087])).

tff(c_2112,plain,
    ( ~ v16_lattices('#skF_9')
    | ~ v15_lattices('#skF_9')
    | ~ v16_lattices('#skF_8')
    | ~ v15_lattices('#skF_8')
    | ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2109,c_2104])).

tff(c_2115,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_1995,c_1944,c_1992,c_1941,c_2112])).

tff(c_2117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_2115])).

tff(c_2119,plain,(
    v2_struct_0(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_2306,plain,(
    ! [A_304,B_305] :
      ( ~ v2_struct_0(k7_filter_1(A_304,B_305))
      | ~ l3_lattices(B_305)
      | v2_struct_0(B_305)
      | ~ l3_lattices(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2321,plain,
    ( ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2119,c_2306])).

tff(c_2328,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_168,c_2321])).

tff(c_2330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_2328])).

tff(c_2332,plain,(
    ~ v10_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_2572,plain,
    ( ~ l3_lattices('#skF_9')
    | ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2569,c_2332])).

tff(c_2575,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_174,c_170,c_168,c_2572])).

tff(c_2577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_2575])).

tff(c_2579,plain,(
    ~ l3_lattices(k7_filter_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_2799,plain,
    ( ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2796,c_2579])).

tff(c_2802,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_168,c_2799])).

tff(c_2804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_172,c_2802])).

%------------------------------------------------------------------------------
