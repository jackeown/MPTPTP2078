%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1452+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:56 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 761 expanded)
%              Number of leaves         :   22 ( 271 expanded)
%              Depth                    :   10
%              Number of atoms          :  621 (5323 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_lattices > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > k7_filter_1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

tff(k7_filter_1,type,(
    k7_filter_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(v16_lattices,type,(
    v16_lattices: $i > $o )).

tff(v15_lattices,type,(
    v15_lattices: $i > $o )).

tff(f_236,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

tff(f_103,axiom,(
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

tff(f_145,axiom,(
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

tff(f_193,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( ~ v2_struct_0(k7_filter_1(A,B))
        & v3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_filter_1)).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_86,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_80,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_2175,plain,(
    ! [A_387,B_388] :
      ( l3_lattices(k7_filter_1(A_387,B_388))
      | ~ l3_lattices(B_388)
      | v2_struct_0(B_388)
      | ~ l3_lattices(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_88,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_82,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_1920,plain,(
    ! [A_351,B_352] :
      ( v10_lattices(k7_filter_1(A_351,B_352))
      | ~ l3_lattices(B_352)
      | ~ v10_lattices(B_352)
      | v2_struct_0(B_352)
      | ~ l3_lattices(A_351)
      | ~ v10_lattices(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1810,plain,(
    ! [A_339,B_340] :
      ( l3_lattices(k7_filter_1(A_339,B_340))
      | ~ l3_lattices(B_340)
      | v2_struct_0(B_340)
      | ~ l3_lattices(A_339)
      | v2_struct_0(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_168,plain,
    ( v17_lattices('#skF_2')
    | ~ v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_207,plain,(
    ~ v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_214,plain,(
    ! [A_16] :
      ( v15_lattices(A_16)
      | ~ v17_lattices(A_16)
      | v2_struct_0(A_16)
      | ~ l3_lattices(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_223,plain,
    ( v15_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_214,c_90])).

tff(c_232,plain,
    ( v15_lattices('#skF_1')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_223])).

tff(c_1171,plain,(
    ~ v17_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_1211,plain,(
    ! [A_227] :
      ( v17_lattices(A_227)
      | ~ v16_lattices(A_227)
      | ~ v15_lattices(A_227)
      | ~ v11_lattices(A_227)
      | v2_struct_0(A_227)
      | ~ l3_lattices(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1220,plain,
    ( v17_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1211,c_90])).

tff(c_1229,plain,
    ( v17_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1220])).

tff(c_1230,plain,
    ( ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ v11_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1171,c_1229])).

tff(c_1231,plain,(
    ~ v11_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1230])).

tff(c_150,plain,
    ( v17_lattices('#skF_2')
    | v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_209,plain,(
    v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_122,plain,
    ( v17_lattices('#skF_1')
    | l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_210,plain,(
    l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_132,plain,
    ( v17_lattices('#skF_2')
    | v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_208,plain,(
    v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_1191,plain,(
    ! [A_224] :
      ( v11_lattices(A_224)
      | ~ v17_lattices(A_224)
      | v2_struct_0(A_224)
      | ~ l3_lattices(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1194,plain,
    ( v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1191,c_207])).

tff(c_1203,plain,(
    v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_208,c_1194])).

tff(c_1318,plain,(
    ! [A_252,B_253] :
      ( v11_lattices(A_252)
      | ~ l3_lattices(k7_filter_1(A_252,B_253))
      | ~ v11_lattices(k7_filter_1(A_252,B_253))
      | ~ v10_lattices(k7_filter_1(A_252,B_253))
      | v2_struct_0(k7_filter_1(A_252,B_253))
      | ~ l3_lattices(B_253)
      | ~ v10_lattices(B_253)
      | v2_struct_0(B_253)
      | ~ l3_lattices(A_252)
      | ~ v10_lattices(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1324,plain,
    ( v11_lattices('#skF_1')
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1318,c_207])).

tff(c_1328,plain,
    ( v11_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_209,c_1203,c_210,c_1324])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1231,c_1328])).

tff(c_1331,plain,
    ( ~ v15_lattices('#skF_1')
    | ~ v16_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1230])).

tff(c_1334,plain,(
    ~ v16_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1331])).

tff(c_217,plain,
    ( v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_214,c_207])).

tff(c_226,plain,(
    v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_208,c_217])).

tff(c_1172,plain,(
    ! [A_223] :
      ( v16_lattices(A_223)
      | ~ v17_lattices(A_223)
      | v2_struct_0(A_223)
      | ~ l3_lattices(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1175,plain,
    ( v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1172,c_207])).

tff(c_1184,plain,(
    v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_208,c_1175])).

tff(c_1492,plain,(
    ! [A_290,B_291] :
      ( v16_lattices(A_290)
      | ~ l3_lattices(k7_filter_1(A_290,B_291))
      | ~ v16_lattices(k7_filter_1(A_290,B_291))
      | ~ v15_lattices(k7_filter_1(A_290,B_291))
      | ~ v10_lattices(k7_filter_1(A_290,B_291))
      | v2_struct_0(k7_filter_1(A_290,B_291))
      | ~ l3_lattices(B_291)
      | ~ v10_lattices(B_291)
      | v2_struct_0(B_291)
      | ~ l3_lattices(A_290)
      | ~ v10_lattices(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1498,plain,
    ( v16_lattices('#skF_1')
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1492,c_207])).

tff(c_1502,plain,
    ( v16_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_209,c_226,c_1184,c_210,c_1498])).

tff(c_1504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1334,c_1502])).

tff(c_1505,plain,(
    ~ v15_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1331])).

tff(c_1688,plain,(
    ! [A_330,B_331] :
      ( v15_lattices(A_330)
      | ~ l3_lattices(k7_filter_1(A_330,B_331))
      | ~ v16_lattices(k7_filter_1(A_330,B_331))
      | ~ v15_lattices(k7_filter_1(A_330,B_331))
      | ~ v10_lattices(k7_filter_1(A_330,B_331))
      | v2_struct_0(k7_filter_1(A_330,B_331))
      | ~ l3_lattices(B_331)
      | ~ v10_lattices(B_331)
      | v2_struct_0(B_331)
      | ~ l3_lattices(A_330)
      | ~ v10_lattices(A_330)
      | v2_struct_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1694,plain,
    ( v15_lattices('#skF_1')
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1688,c_207])).

tff(c_1698,plain,
    ( v15_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_209,c_226,c_1184,c_210,c_1694])).

tff(c_1700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1505,c_1698])).

tff(c_1702,plain,(
    v17_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_220,plain,
    ( v15_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_214,c_84])).

tff(c_229,plain,
    ( v15_lattices('#skF_2')
    | ~ v17_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_220])).

tff(c_233,plain,(
    ~ v17_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_791,plain,(
    ! [A_142] :
      ( v17_lattices(A_142)
      | ~ v16_lattices(A_142)
      | ~ v15_lattices(A_142)
      | ~ v11_lattices(A_142)
      | v2_struct_0(A_142)
      | ~ l3_lattices(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_800,plain,
    ( v17_lattices('#skF_2')
    | ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v11_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_791,c_84])).

tff(c_810,plain,
    ( v17_lattices('#skF_2')
    | ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v11_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_800])).

tff(c_811,plain,
    ( ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v11_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_810])).

tff(c_816,plain,(
    ~ v11_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_738,plain,(
    ! [A_134] :
      ( v11_lattices(A_134)
      | ~ v17_lattices(A_134)
      | v2_struct_0(A_134)
      | ~ l3_lattices(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_741,plain,
    ( v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_738,c_207])).

tff(c_750,plain,(
    v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_208,c_741])).

tff(c_847,plain,(
    ! [B_157,A_158] :
      ( v11_lattices(B_157)
      | ~ l3_lattices(k7_filter_1(A_158,B_157))
      | ~ v11_lattices(k7_filter_1(A_158,B_157))
      | ~ v10_lattices(k7_filter_1(A_158,B_157))
      | v2_struct_0(k7_filter_1(A_158,B_157))
      | ~ l3_lattices(B_157)
      | ~ v10_lattices(B_157)
      | v2_struct_0(B_157)
      | ~ l3_lattices(A_158)
      | ~ v10_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_853,plain,
    ( v11_lattices('#skF_2')
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_847,c_207])).

tff(c_857,plain,
    ( v11_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_209,c_750,c_210,c_853])).

tff(c_859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_816,c_857])).

tff(c_860,plain,
    ( ~ v15_lattices('#skF_2')
    | ~ v16_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_862,plain,(
    ~ v16_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_860])).

tff(c_757,plain,(
    ! [A_135] :
      ( v16_lattices(A_135)
      | ~ v17_lattices(A_135)
      | v2_struct_0(A_135)
      | ~ l3_lattices(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_760,plain,
    ( v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_757,c_207])).

tff(c_769,plain,(
    v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_208,c_760])).

tff(c_1026,plain,(
    ! [B_193,A_194] :
      ( v16_lattices(B_193)
      | ~ l3_lattices(k7_filter_1(A_194,B_193))
      | ~ v16_lattices(k7_filter_1(A_194,B_193))
      | ~ v15_lattices(k7_filter_1(A_194,B_193))
      | ~ v10_lattices(k7_filter_1(A_194,B_193))
      | v2_struct_0(k7_filter_1(A_194,B_193))
      | ~ l3_lattices(B_193)
      | ~ v10_lattices(B_193)
      | v2_struct_0(B_193)
      | ~ l3_lattices(A_194)
      | ~ v10_lattices(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1032,plain,
    ( v16_lattices('#skF_2')
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1026,c_207])).

tff(c_1036,plain,
    ( v16_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_209,c_226,c_769,c_210,c_1032])).

tff(c_1038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_862,c_1036])).

tff(c_1039,plain,(
    ~ v15_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_1156,plain,(
    ! [B_221,A_222] :
      ( v15_lattices(B_221)
      | ~ l3_lattices(k7_filter_1(A_222,B_221))
      | ~ v16_lattices(k7_filter_1(A_222,B_221))
      | ~ v15_lattices(k7_filter_1(A_222,B_221))
      | ~ v10_lattices(k7_filter_1(A_222,B_221))
      | v2_struct_0(k7_filter_1(A_222,B_221))
      | ~ l3_lattices(B_221)
      | ~ v10_lattices(B_221)
      | v2_struct_0(B_221)
      | ~ l3_lattices(A_222)
      | ~ v10_lattices(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1162,plain,
    ( v15_lattices('#skF_2')
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1156,c_207])).

tff(c_1166,plain,
    ( v15_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_209,c_226,c_769,c_210,c_1162])).

tff(c_1168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1039,c_1166])).

tff(c_1170,plain,(
    v17_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_92,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_181,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ v10_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_92])).

tff(c_187,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_181])).

tff(c_193,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_187])).

tff(c_194,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_193])).

tff(c_200,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_194])).

tff(c_206,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_200])).

tff(c_1723,plain,(
    v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1702,c_1170,c_209,c_208,c_210,c_206])).

tff(c_1724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_1723])).

tff(c_1726,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_1813,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1810,c_1726])).

tff(c_1816,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_1813])).

tff(c_1818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1816])).

tff(c_1820,plain,(
    ~ v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1923,plain,
    ( ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1920,c_1820])).

tff(c_1926,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_1923])).

tff(c_1928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1926])).

tff(c_1930,plain,(
    ~ v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_140,plain,
    ( v17_lattices('#skF_1')
    | v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_1935,plain,(
    v17_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1930,c_140])).

tff(c_1936,plain,(
    ! [A_353] :
      ( v15_lattices(A_353)
      | ~ v17_lattices(A_353)
      | v2_struct_0(A_353)
      | ~ l3_lattices(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1945,plain,
    ( v15_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1936,c_90])).

tff(c_1954,plain,(
    v15_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1935,c_1945])).

tff(c_1974,plain,(
    ! [A_355] :
      ( v16_lattices(A_355)
      | ~ v17_lattices(A_355)
      | v2_struct_0(A_355)
      | ~ l3_lattices(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1983,plain,
    ( v16_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1974,c_90])).

tff(c_1992,plain,(
    v16_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1935,c_1983])).

tff(c_1929,plain,(
    v17_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_1942,plain,
    ( v15_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1936,c_84])).

tff(c_1951,plain,(
    v15_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1929,c_1942])).

tff(c_1980,plain,
    ( v16_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1974,c_84])).

tff(c_1989,plain,(
    v16_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1929,c_1980])).

tff(c_2068,plain,(
    ! [A_379,B_380] :
      ( v15_lattices(k7_filter_1(A_379,B_380))
      | ~ v16_lattices(B_380)
      | ~ v15_lattices(B_380)
      | ~ v16_lattices(A_379)
      | ~ v15_lattices(A_379)
      | ~ l3_lattices(B_380)
      | ~ v10_lattices(B_380)
      | v2_struct_0(B_380)
      | ~ l3_lattices(A_379)
      | ~ v10_lattices(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2052,plain,(
    ! [A_373,B_374] :
      ( v16_lattices(k7_filter_1(A_373,B_374))
      | ~ v16_lattices(B_374)
      | ~ v15_lattices(B_374)
      | ~ v16_lattices(A_373)
      | ~ v15_lattices(A_373)
      | ~ l3_lattices(B_374)
      | ~ v10_lattices(B_374)
      | v2_struct_0(B_374)
      | ~ l3_lattices(A_373)
      | ~ v10_lattices(A_373)
      | v2_struct_0(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1955,plain,(
    ! [A_354] :
      ( v11_lattices(A_354)
      | ~ v17_lattices(A_354)
      | v2_struct_0(A_354)
      | ~ l3_lattices(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1964,plain,
    ( v11_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1955,c_90])).

tff(c_1973,plain,(
    v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1935,c_1964])).

tff(c_1961,plain,
    ( v11_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1955,c_84])).

tff(c_1970,plain,(
    v11_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1929,c_1961])).

tff(c_2034,plain,(
    ! [A_365,B_366] :
      ( v11_lattices(k7_filter_1(A_365,B_366))
      | ~ v11_lattices(B_366)
      | ~ v11_lattices(A_365)
      | ~ l3_lattices(B_366)
      | ~ v10_lattices(B_366)
      | v2_struct_0(B_366)
      | ~ l3_lattices(A_365)
      | ~ v10_lattices(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1931,plain,(
    l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_2007,plain,(
    ! [A_360] :
      ( v17_lattices(A_360)
      | ~ v16_lattices(A_360)
      | ~ v15_lattices(A_360)
      | ~ v11_lattices(A_360)
      | v2_struct_0(A_360)
      | ~ l3_lattices(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2013,plain,
    ( v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2007,c_207])).

tff(c_2023,plain,
    ( v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1931,c_2013])).

tff(c_2024,plain,
    ( ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1930,c_2023])).

tff(c_2032,plain,(
    ~ v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2024])).

tff(c_2037,plain,
    ( ~ v11_lattices('#skF_2')
    | ~ v11_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2034,c_2032])).

tff(c_2040,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_1973,c_1970,c_2037])).

tff(c_2042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_2040])).

tff(c_2043,plain,
    ( ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2024])).

tff(c_2045,plain,(
    ~ v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2043])).

tff(c_2055,plain,
    ( ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2052,c_2045])).

tff(c_2058,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_1954,c_1992,c_1951,c_1989,c_2055])).

tff(c_2060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_2058])).

tff(c_2061,plain,(
    ~ v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2043])).

tff(c_2071,plain,
    ( ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2068,c_2061])).

tff(c_2074,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_1954,c_1992,c_1951,c_1989,c_2071])).

tff(c_2076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_2074])).

tff(c_2078,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_2178,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2175,c_2078])).

tff(c_2181,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_2178])).

tff(c_2183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_2181])).

tff(c_2185,plain,(
    v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_2235,plain,(
    ! [A_392,B_393] :
      ( ~ v2_struct_0(k7_filter_1(A_392,B_393))
      | ~ l3_lattices(B_393)
      | v2_struct_0(B_393)
      | ~ l3_lattices(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2247,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2185,c_2235])).

tff(c_2253,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_2247])).

tff(c_2255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_2253])).

%------------------------------------------------------------------------------
