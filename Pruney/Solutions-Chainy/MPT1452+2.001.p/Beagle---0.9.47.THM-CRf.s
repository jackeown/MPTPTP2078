%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:37 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 814 expanded)
%              Number of leaves         :   20 ( 290 expanded)
%              Depth                    :   10
%              Number of atoms          :  650 (5714 expanded)
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

tff(f_204,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_filter_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

tff(f_57,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v17_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_lattices)).

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_filter_1)).

tff(f_161,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_filter_1)).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_80,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_78,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1927,plain,(
    ! [A_367,B_368] :
      ( l3_lattices(k7_filter_1(A_367,B_368))
      | ~ l3_lattices(B_368)
      | v2_struct_0(B_368)
      | ~ l3_lattices(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_160,plain,
    ( v17_lattices('#skF_2')
    | ~ v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_199,plain,(
    ~ v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_206,plain,(
    ! [A_12] :
      ( v16_lattices(A_12)
      | ~ v17_lattices(A_12)
      | v2_struct_0(A_12)
      | ~ l3_lattices(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_215,plain,
    ( v16_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_82])).

tff(c_224,plain,
    ( v16_lattices('#skF_1')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_215])).

tff(c_1279,plain,(
    ~ v17_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_1302,plain,(
    ! [A_255] :
      ( v17_lattices(A_255)
      | ~ v16_lattices(A_255)
      | ~ v15_lattices(A_255)
      | ~ v11_lattices(A_255)
      | v2_struct_0(A_255)
      | ~ l3_lattices(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1311,plain,
    ( v17_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1302,c_82])).

tff(c_1320,plain,
    ( v17_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1311])).

tff(c_1321,plain,
    ( ~ v16_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ v11_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_1320])).

tff(c_1322,plain,(
    ~ v11_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1321])).

tff(c_142,plain,
    ( v17_lattices('#skF_2')
    | v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_202,plain,(
    v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_114,plain,
    ( v17_lattices('#skF_1')
    | l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_201,plain,(
    l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_132,plain,
    ( v17_lattices('#skF_1')
    | v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_200,plain,(
    v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_1282,plain,(
    ! [A_252] :
      ( v11_lattices(A_252)
      | ~ v17_lattices(A_252)
      | v2_struct_0(A_252)
      | ~ l3_lattices(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1285,plain,
    ( v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1282,c_199])).

tff(c_1294,plain,(
    v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_200,c_1285])).

tff(c_1398,plain,(
    ! [A_278,B_279] :
      ( v11_lattices(A_278)
      | ~ l3_lattices(k7_filter_1(A_278,B_279))
      | ~ v11_lattices(k7_filter_1(A_278,B_279))
      | ~ v10_lattices(k7_filter_1(A_278,B_279))
      | v2_struct_0(k7_filter_1(A_278,B_279))
      | ~ l3_lattices(B_279)
      | ~ v10_lattices(B_279)
      | v2_struct_0(B_279)
      | ~ l3_lattices(A_278)
      | ~ v10_lattices(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1407,plain,
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
    inference(resolution,[status(thm)],[c_1398,c_199])).

tff(c_1412,plain,
    ( v11_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_202,c_1294,c_201,c_1407])).

tff(c_1414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1322,c_1412])).

tff(c_1415,plain,
    ( ~ v15_lattices('#skF_1')
    | ~ v16_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1321])).

tff(c_1417,plain,(
    ~ v16_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1415])).

tff(c_1260,plain,(
    ! [A_251] :
      ( v15_lattices(A_251)
      | ~ v17_lattices(A_251)
      | v2_struct_0(A_251)
      | ~ l3_lattices(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1263,plain,
    ( v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1260,c_199])).

tff(c_1272,plain,(
    v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_200,c_1263])).

tff(c_209,plain,
    ( v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_206,c_199])).

tff(c_218,plain,(
    v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_200,c_209])).

tff(c_1549,plain,(
    ! [A_310,B_311] :
      ( v16_lattices(A_310)
      | ~ l3_lattices(k7_filter_1(A_310,B_311))
      | ~ v16_lattices(k7_filter_1(A_310,B_311))
      | ~ v15_lattices(k7_filter_1(A_310,B_311))
      | ~ v10_lattices(k7_filter_1(A_310,B_311))
      | v2_struct_0(k7_filter_1(A_310,B_311))
      | ~ l3_lattices(B_311)
      | ~ v10_lattices(B_311)
      | v2_struct_0(B_311)
      | ~ l3_lattices(A_310)
      | ~ v10_lattices(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1558,plain,
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
    inference(resolution,[status(thm)],[c_1549,c_199])).

tff(c_1563,plain,
    ( v16_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_202,c_1272,c_218,c_201,c_1558])).

tff(c_1565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1417,c_1563])).

tff(c_1566,plain,(
    ~ v15_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1415])).

tff(c_1683,plain,(
    ! [A_340,B_341] :
      ( v15_lattices(A_340)
      | ~ l3_lattices(k7_filter_1(A_340,B_341))
      | ~ v16_lattices(k7_filter_1(A_340,B_341))
      | ~ v15_lattices(k7_filter_1(A_340,B_341))
      | ~ v10_lattices(k7_filter_1(A_340,B_341))
      | v2_struct_0(k7_filter_1(A_340,B_341))
      | ~ l3_lattices(B_341)
      | ~ v10_lattices(B_341)
      | v2_struct_0(B_341)
      | ~ l3_lattices(A_340)
      | ~ v10_lattices(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1692,plain,
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
    inference(resolution,[status(thm)],[c_1683,c_199])).

tff(c_1697,plain,
    ( v15_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_202,c_1272,c_218,c_201,c_1692])).

tff(c_1699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1566,c_1697])).

tff(c_1701,plain,(
    v17_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_212,plain,
    ( v16_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_206,c_76])).

tff(c_221,plain,
    ( v16_lattices('#skF_2')
    | ~ v17_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_212])).

tff(c_225,plain,(
    ~ v17_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_917,plain,(
    ! [A_170] :
      ( v17_lattices(A_170)
      | ~ v16_lattices(A_170)
      | ~ v15_lattices(A_170)
      | ~ v11_lattices(A_170)
      | v2_struct_0(A_170)
      | ~ l3_lattices(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_923,plain,
    ( v17_lattices('#skF_2')
    | ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v11_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_917,c_76])).

tff(c_932,plain,
    ( v17_lattices('#skF_2')
    | ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v11_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_923])).

tff(c_933,plain,
    ( ~ v16_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ v11_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_932])).

tff(c_937,plain,(
    ~ v11_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_875,plain,(
    ! [A_166] :
      ( v11_lattices(A_166)
      | ~ v17_lattices(A_166)
      | v2_struct_0(A_166)
      | ~ l3_lattices(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_878,plain,
    ( v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_875,c_199])).

tff(c_887,plain,(
    v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_200,c_878])).

tff(c_1010,plain,(
    ! [B_193,A_194] :
      ( v11_lattices(B_193)
      | ~ l3_lattices(k7_filter_1(A_194,B_193))
      | ~ v11_lattices(k7_filter_1(A_194,B_193))
      | ~ v10_lattices(k7_filter_1(A_194,B_193))
      | v2_struct_0(k7_filter_1(A_194,B_193))
      | ~ l3_lattices(B_193)
      | ~ v10_lattices(B_193)
      | v2_struct_0(B_193)
      | ~ l3_lattices(A_194)
      | ~ v10_lattices(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1019,plain,
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
    inference(resolution,[status(thm)],[c_1010,c_199])).

tff(c_1024,plain,
    ( v11_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_202,c_887,c_201,c_1019])).

tff(c_1026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_937,c_1024])).

tff(c_1027,plain,
    ( ~ v15_lattices('#skF_2')
    | ~ v16_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_1029,plain,(
    ~ v16_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1027])).

tff(c_894,plain,(
    ! [A_167] :
      ( v15_lattices(A_167)
      | ~ v17_lattices(A_167)
      | v2_struct_0(A_167)
      | ~ l3_lattices(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_897,plain,
    ( v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_894,c_199])).

tff(c_906,plain,(
    v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_200,c_897])).

tff(c_1126,plain,(
    ! [B_221,A_222] :
      ( v16_lattices(B_221)
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
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1135,plain,
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
    inference(resolution,[status(thm)],[c_1126,c_199])).

tff(c_1140,plain,
    ( v16_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_202,c_906,c_218,c_201,c_1135])).

tff(c_1142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1029,c_1140])).

tff(c_1143,plain,(
    ~ v15_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1027])).

tff(c_1241,plain,(
    ! [B_249,A_250] :
      ( v15_lattices(B_249)
      | ~ l3_lattices(k7_filter_1(A_250,B_249))
      | ~ v16_lattices(k7_filter_1(A_250,B_249))
      | ~ v15_lattices(k7_filter_1(A_250,B_249))
      | ~ v10_lattices(k7_filter_1(A_250,B_249))
      | v2_struct_0(k7_filter_1(A_250,B_249))
      | ~ l3_lattices(B_249)
      | ~ v10_lattices(B_249)
      | v2_struct_0(B_249)
      | ~ l3_lattices(A_250)
      | ~ v10_lattices(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1250,plain,
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
    inference(resolution,[status(thm)],[c_1241,c_199])).

tff(c_1255,plain,
    ( v15_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_202,c_906,c_218,c_201,c_1250])).

tff(c_1257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1143,c_1255])).

tff(c_1259,plain,(
    v17_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_84,plain,
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
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_173,plain,
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
    inference(negUnitSimplification,[status(thm)],[c_82,c_84])).

tff(c_179,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_173])).

tff(c_185,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_179])).

tff(c_186,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_185])).

tff(c_192,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_186])).

tff(c_198,plain,
    ( ~ l3_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v10_lattices(k7_filter_1('#skF_1','#skF_2'))
    | v2_struct_0(k7_filter_1('#skF_1','#skF_2'))
    | ~ v17_lattices('#skF_2')
    | ~ v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_192])).

tff(c_1766,plain,(
    v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_1259,c_202,c_200,c_201,c_198])).

tff(c_1767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_1766])).

tff(c_1769,plain,(
    ~ v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_150,plain,
    ( v17_lattices('#skF_1')
    | v10_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1772,plain,(
    v17_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1769,c_150])).

tff(c_1795,plain,(
    ! [A_355] :
      ( v11_lattices(A_355)
      | ~ v17_lattices(A_355)
      | v2_struct_0(A_355)
      | ~ l3_lattices(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1804,plain,
    ( v11_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1795,c_82])).

tff(c_1813,plain,(
    v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1772,c_1804])).

tff(c_1768,plain,(
    v17_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1801,plain,
    ( v11_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1795,c_76])).

tff(c_1810,plain,(
    v11_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1768,c_1801])).

tff(c_1854,plain,(
    ! [A_362,B_363] :
      ( v10_lattices(k7_filter_1(A_362,B_363))
      | ~ v11_lattices(B_363)
      | ~ v11_lattices(A_362)
      | ~ l3_lattices(B_363)
      | ~ v10_lattices(B_363)
      | v2_struct_0(B_363)
      | ~ l3_lattices(A_362)
      | ~ v10_lattices(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1857,plain,
    ( ~ v11_lattices('#skF_2')
    | ~ v11_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1854,c_1769])).

tff(c_1860,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_1813,c_1810,c_1857])).

tff(c_1862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1860])).

tff(c_1864,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_1930,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1927,c_1864])).

tff(c_1933,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_1930])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1933])).

tff(c_1936,plain,(
    v17_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_1981,plain,(
    ! [A_371] :
      ( v15_lattices(A_371)
      | ~ v17_lattices(A_371)
      | v2_struct_0(A_371)
      | ~ l3_lattices(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1990,plain,
    ( v15_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1981,c_82])).

tff(c_1997,plain,(
    v15_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1936,c_1990])).

tff(c_1947,plain,(
    ! [A_369] :
      ( v16_lattices(A_369)
      | ~ v17_lattices(A_369)
      | v2_struct_0(A_369)
      | ~ l3_lattices(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1956,plain,
    ( v16_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1947,c_82])).

tff(c_1963,plain,(
    v16_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1936,c_1956])).

tff(c_1937,plain,(
    ~ v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_124,plain,
    ( v17_lattices('#skF_2')
    | v17_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1939,plain,(
    v17_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1937,c_124])).

tff(c_1987,plain,
    ( v15_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1981,c_76])).

tff(c_1994,plain,(
    v15_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1939,c_1987])).

tff(c_1953,plain,
    ( v16_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1947,c_76])).

tff(c_1960,plain,(
    v16_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1939,c_1953])).

tff(c_2126,plain,(
    ! [A_397,B_398] :
      ( v15_lattices(k7_filter_1(A_397,B_398))
      | ~ v16_lattices(B_398)
      | ~ v15_lattices(B_398)
      | ~ v16_lattices(A_397)
      | ~ v15_lattices(A_397)
      | ~ l3_lattices(B_398)
      | ~ v10_lattices(B_398)
      | v2_struct_0(B_398)
      | ~ l3_lattices(A_397)
      | ~ v10_lattices(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1964,plain,(
    ! [A_370] :
      ( v11_lattices(A_370)
      | ~ v17_lattices(A_370)
      | v2_struct_0(A_370)
      | ~ l3_lattices(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1973,plain,
    ( v11_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_1964,c_82])).

tff(c_1980,plain,(
    v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1936,c_1973])).

tff(c_1970,plain,
    ( v11_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_1964,c_76])).

tff(c_1977,plain,(
    v11_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1939,c_1970])).

tff(c_2097,plain,(
    ! [A_391,B_392] :
      ( v11_lattices(k7_filter_1(A_391,B_392))
      | ~ v11_lattices(B_392)
      | ~ v11_lattices(A_391)
      | ~ l3_lattices(B_392)
      | ~ v10_lattices(B_392)
      | v2_struct_0(B_392)
      | ~ l3_lattices(A_391)
      | ~ v10_lattices(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2068,plain,(
    ! [A_387,B_388] :
      ( v16_lattices(k7_filter_1(A_387,B_388))
      | ~ v16_lattices(B_388)
      | ~ v15_lattices(B_388)
      | ~ v16_lattices(A_387)
      | ~ v15_lattices(A_387)
      | ~ l3_lattices(B_388)
      | ~ v10_lattices(B_388)
      | v2_struct_0(B_388)
      | ~ l3_lattices(A_387)
      | ~ v10_lattices(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_14,plain,(
    ! [A_3,B_4] :
      ( l3_lattices(k7_filter_1(A_3,B_4))
      | ~ l3_lattices(B_4)
      | v2_struct_0(B_4)
      | ~ l3_lattices(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1998,plain,(
    ! [A_372] :
      ( v17_lattices(A_372)
      | ~ v16_lattices(A_372)
      | ~ v15_lattices(A_372)
      | ~ v11_lattices(A_372)
      | v2_struct_0(A_372)
      | ~ l3_lattices(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2001,plain,
    ( v17_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1998,c_199])).

tff(c_2010,plain,
    ( ~ v16_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1937,c_2001])).

tff(c_2019,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2010])).

tff(c_2022,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_2019])).

tff(c_2025,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_2022])).

tff(c_2027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_2025])).

tff(c_2028,plain,
    ( ~ v11_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2010])).

tff(c_2031,plain,(
    ~ v16_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2028])).

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
    inference(resolution,[status(thm)],[c_2068,c_2031])).

tff(c_2074,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_1997,c_1963,c_1994,c_1960,c_2071])).

tff(c_2076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_2074])).

tff(c_2077,plain,
    ( ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2028])).

tff(c_2079,plain,(
    ~ v11_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2077])).

tff(c_2100,plain,
    ( ~ v11_lattices('#skF_2')
    | ~ v11_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2097,c_2079])).

tff(c_2103,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_1980,c_1977,c_2100])).

tff(c_2105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_2103])).

tff(c_2106,plain,(
    ~ v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2077])).

tff(c_2129,plain,
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
    inference(resolution,[status(thm)],[c_2126,c_2106])).

tff(c_2132,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_1997,c_1963,c_1994,c_1960,c_2129])).

tff(c_2134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_2132])).

tff(c_2136,plain,(
    v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_168,plain,
    ( v17_lattices('#skF_1')
    | ~ v2_struct_0(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2143,plain,(
    v17_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_168])).

tff(c_2158,plain,(
    ! [A_400] :
      ( v11_lattices(A_400)
      | ~ v17_lattices(A_400)
      | v2_struct_0(A_400)
      | ~ l3_lattices(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2164,plain,
    ( v11_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2158,c_82])).

tff(c_2170,plain,(
    v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2143,c_2164])).

tff(c_2135,plain,(
    v17_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_2161,plain,
    ( v11_lattices('#skF_2')
    | ~ v17_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_2158,c_76])).

tff(c_2167,plain,(
    v11_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2135,c_2161])).

tff(c_2200,plain,(
    ! [A_409,B_410] :
      ( ~ v2_struct_0(k7_filter_1(A_409,B_410))
      | ~ v11_lattices(B_410)
      | ~ v11_lattices(A_409)
      | ~ l3_lattices(B_410)
      | ~ v10_lattices(B_410)
      | v2_struct_0(B_410)
      | ~ l3_lattices(A_409)
      | ~ v10_lattices(A_409)
      | v2_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2215,plain,
    ( ~ v11_lattices('#skF_2')
    | ~ v11_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2136,c_2200])).

tff(c_2222,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_2170,c_2167,c_2215])).

tff(c_2224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_2222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.91  
% 4.75/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.91  %$ v3_lattices > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > k7_filter_1 > #nlpp > #skF_2 > #skF_1
% 4.75/1.91  
% 4.75/1.91  %Foreground sorts:
% 4.75/1.91  
% 4.75/1.91  
% 4.75/1.91  %Background operators:
% 4.75/1.91  
% 4.75/1.91  
% 4.75/1.91  %Foreground operators:
% 4.75/1.91  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.75/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.75/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.91  tff(v17_lattices, type, v17_lattices: $i > $o).
% 4.75/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.75/1.91  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.75/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.91  tff(v11_lattices, type, v11_lattices: $i > $o).
% 4.75/1.91  tff(k7_filter_1, type, k7_filter_1: ($i * $i) > $i).
% 4.75/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.91  tff(v3_lattices, type, v3_lattices: $i > $o).
% 4.75/1.91  tff(v16_lattices, type, v16_lattices: $i > $o).
% 4.75/1.91  tff(v15_lattices, type, v15_lattices: $i > $o).
% 4.75/1.91  
% 5.16/1.94  tff(f_204, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((((((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) & ~v2_struct_0(B)) & v10_lattices(B)) & v17_lattices(B)) & l3_lattices(B)) <=> (((~v2_struct_0(k7_filter_1(A, B)) & v10_lattices(k7_filter_1(A, B))) & v17_lattices(k7_filter_1(A, B))) & l3_lattices(k7_filter_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_filter_1)).
% 5.16/1.94  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & l3_lattices(A)) & ~v2_struct_0(B)) & l3_lattices(B)) => (v3_lattices(k7_filter_1(A, B)) & l3_lattices(k7_filter_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_filter_1)).
% 5.16/1.94  tff(f_41, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v17_lattices(A)) => (((~v2_struct_0(A) & v11_lattices(A)) & v15_lattices(A)) & v16_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_lattices)).
% 5.16/1.94  tff(f_57, axiom, (![A]: (l3_lattices(A) => ((((~v2_struct_0(A) & v11_lattices(A)) & v15_lattices(A)) & v16_lattices(A)) => (~v2_struct_0(A) & v17_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_lattices)).
% 5.16/1.94  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((((((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) & ~v2_struct_0(B)) & v10_lattices(B)) & v11_lattices(B)) & l3_lattices(B)) <=> (((~v2_struct_0(k7_filter_1(A, B)) & v10_lattices(k7_filter_1(A, B))) & v11_lattices(k7_filter_1(A, B))) & l3_lattices(k7_filter_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_filter_1)).
% 5.16/1.94  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((((((((((~v2_struct_0(A) & v10_lattices(A)) & v15_lattices(A)) & v16_lattices(A)) & l3_lattices(A)) & ~v2_struct_0(B)) & v10_lattices(B)) & v15_lattices(B)) & v16_lattices(B)) & l3_lattices(B)) <=> ((((~v2_struct_0(k7_filter_1(A, B)) & v10_lattices(k7_filter_1(A, B))) & v15_lattices(k7_filter_1(A, B))) & v16_lattices(k7_filter_1(A, B))) & l3_lattices(k7_filter_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_filter_1)).
% 5.16/1.94  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_80, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_78, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_74, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_72, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_1927, plain, (![A_367, B_368]: (l3_lattices(k7_filter_1(A_367, B_368)) | ~l3_lattices(B_368) | v2_struct_0(B_368) | ~l3_lattices(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.16/1.94  tff(c_160, plain, (v17_lattices('#skF_2') | ~v2_struct_0(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_199, plain, (~v2_struct_0(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 5.16/1.94  tff(c_206, plain, (![A_12]: (v16_lattices(A_12) | ~v17_lattices(A_12) | v2_struct_0(A_12) | ~l3_lattices(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_215, plain, (v16_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_206, c_82])).
% 5.16/1.94  tff(c_224, plain, (v16_lattices('#skF_1') | ~v17_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_215])).
% 5.16/1.94  tff(c_1279, plain, (~v17_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_224])).
% 5.16/1.94  tff(c_1302, plain, (![A_255]: (v17_lattices(A_255) | ~v16_lattices(A_255) | ~v15_lattices(A_255) | ~v11_lattices(A_255) | v2_struct_0(A_255) | ~l3_lattices(A_255))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.16/1.94  tff(c_1311, plain, (v17_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_1302, c_82])).
% 5.16/1.94  tff(c_1320, plain, (v17_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1311])).
% 5.16/1.94  tff(c_1321, plain, (~v16_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~v11_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1279, c_1320])).
% 5.16/1.94  tff(c_1322, plain, (~v11_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_1321])).
% 5.16/1.94  tff(c_142, plain, (v17_lattices('#skF_2') | v10_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_202, plain, (v10_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_142])).
% 5.16/1.94  tff(c_114, plain, (v17_lattices('#skF_1') | l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_201, plain, (l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_114])).
% 5.16/1.94  tff(c_132, plain, (v17_lattices('#skF_1') | v17_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_200, plain, (v17_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_132])).
% 5.16/1.94  tff(c_1282, plain, (![A_252]: (v11_lattices(A_252) | ~v17_lattices(A_252) | v2_struct_0(A_252) | ~l3_lattices(A_252))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_1285, plain, (v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1282, c_199])).
% 5.16/1.94  tff(c_1294, plain, (v11_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_200, c_1285])).
% 5.16/1.94  tff(c_1398, plain, (![A_278, B_279]: (v11_lattices(A_278) | ~l3_lattices(k7_filter_1(A_278, B_279)) | ~v11_lattices(k7_filter_1(A_278, B_279)) | ~v10_lattices(k7_filter_1(A_278, B_279)) | v2_struct_0(k7_filter_1(A_278, B_279)) | ~l3_lattices(B_279) | ~v10_lattices(B_279) | v2_struct_0(B_279) | ~l3_lattices(A_278) | ~v10_lattices(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/1.94  tff(c_1407, plain, (v11_lattices('#skF_1') | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1398, c_199])).
% 5.16/1.94  tff(c_1412, plain, (v11_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_202, c_1294, c_201, c_1407])).
% 5.16/1.94  tff(c_1414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1322, c_1412])).
% 5.16/1.94  tff(c_1415, plain, (~v15_lattices('#skF_1') | ~v16_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_1321])).
% 5.16/1.94  tff(c_1417, plain, (~v16_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_1415])).
% 5.16/1.94  tff(c_1260, plain, (![A_251]: (v15_lattices(A_251) | ~v17_lattices(A_251) | v2_struct_0(A_251) | ~l3_lattices(A_251))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_1263, plain, (v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1260, c_199])).
% 5.16/1.94  tff(c_1272, plain, (v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_200, c_1263])).
% 5.16/1.94  tff(c_209, plain, (v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_206, c_199])).
% 5.16/1.94  tff(c_218, plain, (v16_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_200, c_209])).
% 5.16/1.94  tff(c_1549, plain, (![A_310, B_311]: (v16_lattices(A_310) | ~l3_lattices(k7_filter_1(A_310, B_311)) | ~v16_lattices(k7_filter_1(A_310, B_311)) | ~v15_lattices(k7_filter_1(A_310, B_311)) | ~v10_lattices(k7_filter_1(A_310, B_311)) | v2_struct_0(k7_filter_1(A_310, B_311)) | ~l3_lattices(B_311) | ~v10_lattices(B_311) | v2_struct_0(B_311) | ~l3_lattices(A_310) | ~v10_lattices(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.16/1.94  tff(c_1558, plain, (v16_lattices('#skF_1') | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1549, c_199])).
% 5.16/1.94  tff(c_1563, plain, (v16_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_202, c_1272, c_218, c_201, c_1558])).
% 5.16/1.94  tff(c_1565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1417, c_1563])).
% 5.16/1.94  tff(c_1566, plain, (~v15_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_1415])).
% 5.16/1.94  tff(c_1683, plain, (![A_340, B_341]: (v15_lattices(A_340) | ~l3_lattices(k7_filter_1(A_340, B_341)) | ~v16_lattices(k7_filter_1(A_340, B_341)) | ~v15_lattices(k7_filter_1(A_340, B_341)) | ~v10_lattices(k7_filter_1(A_340, B_341)) | v2_struct_0(k7_filter_1(A_340, B_341)) | ~l3_lattices(B_341) | ~v10_lattices(B_341) | v2_struct_0(B_341) | ~l3_lattices(A_340) | ~v10_lattices(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.16/1.94  tff(c_1692, plain, (v15_lattices('#skF_1') | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1683, c_199])).
% 5.16/1.94  tff(c_1697, plain, (v15_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_202, c_1272, c_218, c_201, c_1692])).
% 5.16/1.94  tff(c_1699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1566, c_1697])).
% 5.16/1.94  tff(c_1701, plain, (v17_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_224])).
% 5.16/1.94  tff(c_212, plain, (v16_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_206, c_76])).
% 5.16/1.94  tff(c_221, plain, (v16_lattices('#skF_2') | ~v17_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_212])).
% 5.16/1.94  tff(c_225, plain, (~v17_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_221])).
% 5.16/1.94  tff(c_917, plain, (![A_170]: (v17_lattices(A_170) | ~v16_lattices(A_170) | ~v15_lattices(A_170) | ~v11_lattices(A_170) | v2_struct_0(A_170) | ~l3_lattices(A_170))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.16/1.94  tff(c_923, plain, (v17_lattices('#skF_2') | ~v16_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~v11_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_917, c_76])).
% 5.16/1.94  tff(c_932, plain, (v17_lattices('#skF_2') | ~v16_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~v11_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_923])).
% 5.16/1.94  tff(c_933, plain, (~v16_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~v11_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_225, c_932])).
% 5.16/1.94  tff(c_937, plain, (~v11_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_933])).
% 5.16/1.94  tff(c_875, plain, (![A_166]: (v11_lattices(A_166) | ~v17_lattices(A_166) | v2_struct_0(A_166) | ~l3_lattices(A_166))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_878, plain, (v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_875, c_199])).
% 5.16/1.94  tff(c_887, plain, (v11_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_200, c_878])).
% 5.16/1.94  tff(c_1010, plain, (![B_193, A_194]: (v11_lattices(B_193) | ~l3_lattices(k7_filter_1(A_194, B_193)) | ~v11_lattices(k7_filter_1(A_194, B_193)) | ~v10_lattices(k7_filter_1(A_194, B_193)) | v2_struct_0(k7_filter_1(A_194, B_193)) | ~l3_lattices(B_193) | ~v10_lattices(B_193) | v2_struct_0(B_193) | ~l3_lattices(A_194) | ~v10_lattices(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/1.94  tff(c_1019, plain, (v11_lattices('#skF_2') | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1010, c_199])).
% 5.16/1.94  tff(c_1024, plain, (v11_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_202, c_887, c_201, c_1019])).
% 5.16/1.94  tff(c_1026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_937, c_1024])).
% 5.16/1.94  tff(c_1027, plain, (~v15_lattices('#skF_2') | ~v16_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_933])).
% 5.16/1.94  tff(c_1029, plain, (~v16_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_1027])).
% 5.16/1.94  tff(c_894, plain, (![A_167]: (v15_lattices(A_167) | ~v17_lattices(A_167) | v2_struct_0(A_167) | ~l3_lattices(A_167))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_897, plain, (v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_894, c_199])).
% 5.16/1.94  tff(c_906, plain, (v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_200, c_897])).
% 5.16/1.94  tff(c_1126, plain, (![B_221, A_222]: (v16_lattices(B_221) | ~l3_lattices(k7_filter_1(A_222, B_221)) | ~v16_lattices(k7_filter_1(A_222, B_221)) | ~v15_lattices(k7_filter_1(A_222, B_221)) | ~v10_lattices(k7_filter_1(A_222, B_221)) | v2_struct_0(k7_filter_1(A_222, B_221)) | ~l3_lattices(B_221) | ~v10_lattices(B_221) | v2_struct_0(B_221) | ~l3_lattices(A_222) | ~v10_lattices(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.16/1.94  tff(c_1135, plain, (v16_lattices('#skF_2') | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1126, c_199])).
% 5.16/1.94  tff(c_1140, plain, (v16_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_202, c_906, c_218, c_201, c_1135])).
% 5.16/1.94  tff(c_1142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1029, c_1140])).
% 5.16/1.94  tff(c_1143, plain, (~v15_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_1027])).
% 5.16/1.94  tff(c_1241, plain, (![B_249, A_250]: (v15_lattices(B_249) | ~l3_lattices(k7_filter_1(A_250, B_249)) | ~v16_lattices(k7_filter_1(A_250, B_249)) | ~v15_lattices(k7_filter_1(A_250, B_249)) | ~v10_lattices(k7_filter_1(A_250, B_249)) | v2_struct_0(k7_filter_1(A_250, B_249)) | ~l3_lattices(B_249) | ~v10_lattices(B_249) | v2_struct_0(B_249) | ~l3_lattices(A_250) | ~v10_lattices(A_250) | v2_struct_0(A_250))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.16/1.94  tff(c_1250, plain, (v15_lattices('#skF_2') | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1241, c_199])).
% 5.16/1.94  tff(c_1255, plain, (v15_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_202, c_906, c_218, c_201, c_1250])).
% 5.16/1.94  tff(c_1257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1143, c_1255])).
% 5.16/1.94  tff(c_1259, plain, (v17_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_221])).
% 5.16/1.94  tff(c_84, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_173, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~v10_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_82, c_84])).
% 5.16/1.94  tff(c_179, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v17_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_173])).
% 5.16/1.94  tff(c_185, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~v17_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_179])).
% 5.16/1.94  tff(c_186, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~v10_lattices('#skF_2') | ~v17_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_185])).
% 5.16/1.94  tff(c_192, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~v17_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_186])).
% 5.16/1.94  tff(c_198, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v10_lattices(k7_filter_1('#skF_1', '#skF_2')) | v2_struct_0(k7_filter_1('#skF_1', '#skF_2')) | ~v17_lattices('#skF_2') | ~v17_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_192])).
% 5.16/1.94  tff(c_1766, plain, (v2_struct_0(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_1259, c_202, c_200, c_201, c_198])).
% 5.16/1.94  tff(c_1767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_1766])).
% 5.16/1.94  tff(c_1769, plain, (~v10_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_142])).
% 5.16/1.94  tff(c_150, plain, (v17_lattices('#skF_1') | v10_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_1772, plain, (v17_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1769, c_150])).
% 5.16/1.94  tff(c_1795, plain, (![A_355]: (v11_lattices(A_355) | ~v17_lattices(A_355) | v2_struct_0(A_355) | ~l3_lattices(A_355))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_1804, plain, (v11_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_1795, c_82])).
% 5.16/1.94  tff(c_1813, plain, (v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1772, c_1804])).
% 5.16/1.94  tff(c_1768, plain, (v17_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_142])).
% 5.16/1.94  tff(c_1801, plain, (v11_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_1795, c_76])).
% 5.16/1.94  tff(c_1810, plain, (v11_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1768, c_1801])).
% 5.16/1.94  tff(c_1854, plain, (![A_362, B_363]: (v10_lattices(k7_filter_1(A_362, B_363)) | ~v11_lattices(B_363) | ~v11_lattices(A_362) | ~l3_lattices(B_363) | ~v10_lattices(B_363) | v2_struct_0(B_363) | ~l3_lattices(A_362) | ~v10_lattices(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/1.94  tff(c_1857, plain, (~v11_lattices('#skF_2') | ~v11_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1854, c_1769])).
% 5.16/1.94  tff(c_1860, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_1813, c_1810, c_1857])).
% 5.16/1.94  tff(c_1862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1860])).
% 5.16/1.94  tff(c_1864, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_114])).
% 5.16/1.94  tff(c_1930, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1927, c_1864])).
% 5.16/1.94  tff(c_1933, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_1930])).
% 5.16/1.94  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1933])).
% 5.16/1.94  tff(c_1936, plain, (v17_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_132])).
% 5.16/1.94  tff(c_1981, plain, (![A_371]: (v15_lattices(A_371) | ~v17_lattices(A_371) | v2_struct_0(A_371) | ~l3_lattices(A_371))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_1990, plain, (v15_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_1981, c_82])).
% 5.16/1.94  tff(c_1997, plain, (v15_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1936, c_1990])).
% 5.16/1.94  tff(c_1947, plain, (![A_369]: (v16_lattices(A_369) | ~v17_lattices(A_369) | v2_struct_0(A_369) | ~l3_lattices(A_369))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_1956, plain, (v16_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_1947, c_82])).
% 5.16/1.94  tff(c_1963, plain, (v16_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1936, c_1956])).
% 5.16/1.94  tff(c_1937, plain, (~v17_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_132])).
% 5.16/1.94  tff(c_124, plain, (v17_lattices('#skF_2') | v17_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_1939, plain, (v17_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1937, c_124])).
% 5.16/1.94  tff(c_1987, plain, (v15_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_1981, c_76])).
% 5.16/1.94  tff(c_1994, plain, (v15_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1939, c_1987])).
% 5.16/1.94  tff(c_1953, plain, (v16_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_1947, c_76])).
% 5.16/1.94  tff(c_1960, plain, (v16_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1939, c_1953])).
% 5.16/1.94  tff(c_2126, plain, (![A_397, B_398]: (v15_lattices(k7_filter_1(A_397, B_398)) | ~v16_lattices(B_398) | ~v15_lattices(B_398) | ~v16_lattices(A_397) | ~v15_lattices(A_397) | ~l3_lattices(B_398) | ~v10_lattices(B_398) | v2_struct_0(B_398) | ~l3_lattices(A_397) | ~v10_lattices(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.16/1.94  tff(c_1964, plain, (![A_370]: (v11_lattices(A_370) | ~v17_lattices(A_370) | v2_struct_0(A_370) | ~l3_lattices(A_370))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_1973, plain, (v11_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_1964, c_82])).
% 5.16/1.94  tff(c_1980, plain, (v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1936, c_1973])).
% 5.16/1.94  tff(c_1970, plain, (v11_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_1964, c_76])).
% 5.16/1.94  tff(c_1977, plain, (v11_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1939, c_1970])).
% 5.16/1.94  tff(c_2097, plain, (![A_391, B_392]: (v11_lattices(k7_filter_1(A_391, B_392)) | ~v11_lattices(B_392) | ~v11_lattices(A_391) | ~l3_lattices(B_392) | ~v10_lattices(B_392) | v2_struct_0(B_392) | ~l3_lattices(A_391) | ~v10_lattices(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/1.94  tff(c_2068, plain, (![A_387, B_388]: (v16_lattices(k7_filter_1(A_387, B_388)) | ~v16_lattices(B_388) | ~v15_lattices(B_388) | ~v16_lattices(A_387) | ~v15_lattices(A_387) | ~l3_lattices(B_388) | ~v10_lattices(B_388) | v2_struct_0(B_388) | ~l3_lattices(A_387) | ~v10_lattices(A_387) | v2_struct_0(A_387))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.16/1.94  tff(c_14, plain, (![A_3, B_4]: (l3_lattices(k7_filter_1(A_3, B_4)) | ~l3_lattices(B_4) | v2_struct_0(B_4) | ~l3_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.16/1.94  tff(c_1998, plain, (![A_372]: (v17_lattices(A_372) | ~v16_lattices(A_372) | ~v15_lattices(A_372) | ~v11_lattices(A_372) | v2_struct_0(A_372) | ~l3_lattices(A_372))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.16/1.94  tff(c_2001, plain, (v17_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1998, c_199])).
% 5.16/1.94  tff(c_2010, plain, (~v16_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1937, c_2001])).
% 5.16/1.94  tff(c_2019, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2010])).
% 5.16/1.94  tff(c_2022, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_2019])).
% 5.16/1.94  tff(c_2025, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_2022])).
% 5.16/1.94  tff(c_2027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_2025])).
% 5.16/1.94  tff(c_2028, plain, (~v11_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v16_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2010])).
% 5.16/1.94  tff(c_2031, plain, (~v16_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2028])).
% 5.16/1.94  tff(c_2071, plain, (~v16_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~v16_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2068, c_2031])).
% 5.16/1.94  tff(c_2074, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_1997, c_1963, c_1994, c_1960, c_2071])).
% 5.16/1.94  tff(c_2076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_2074])).
% 5.16/1.94  tff(c_2077, plain, (~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v11_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2028])).
% 5.16/1.94  tff(c_2079, plain, (~v11_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2077])).
% 5.16/1.94  tff(c_2100, plain, (~v11_lattices('#skF_2') | ~v11_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2097, c_2079])).
% 5.16/1.94  tff(c_2103, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_1980, c_1977, c_2100])).
% 5.16/1.94  tff(c_2105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_2103])).
% 5.16/1.94  tff(c_2106, plain, (~v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2077])).
% 5.16/1.94  tff(c_2129, plain, (~v16_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~v16_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2126, c_2106])).
% 5.16/1.94  tff(c_2132, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_1997, c_1963, c_1994, c_1960, c_2129])).
% 5.16/1.94  tff(c_2134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_2132])).
% 5.16/1.94  tff(c_2136, plain, (v2_struct_0(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_160])).
% 5.16/1.94  tff(c_168, plain, (v17_lattices('#skF_1') | ~v2_struct_0(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.16/1.94  tff(c_2143, plain, (v17_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_168])).
% 5.16/1.94  tff(c_2158, plain, (![A_400]: (v11_lattices(A_400) | ~v17_lattices(A_400) | v2_struct_0(A_400) | ~l3_lattices(A_400))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/1.94  tff(c_2164, plain, (v11_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2158, c_82])).
% 5.16/1.94  tff(c_2170, plain, (v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2143, c_2164])).
% 5.16/1.94  tff(c_2135, plain, (v17_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_160])).
% 5.16/1.94  tff(c_2161, plain, (v11_lattices('#skF_2') | ~v17_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_2158, c_76])).
% 5.16/1.94  tff(c_2167, plain, (v11_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2135, c_2161])).
% 5.16/1.94  tff(c_2200, plain, (![A_409, B_410]: (~v2_struct_0(k7_filter_1(A_409, B_410)) | ~v11_lattices(B_410) | ~v11_lattices(A_409) | ~l3_lattices(B_410) | ~v10_lattices(B_410) | v2_struct_0(B_410) | ~l3_lattices(A_409) | ~v10_lattices(A_409) | v2_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/1.94  tff(c_2215, plain, (~v11_lattices('#skF_2') | ~v11_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2136, c_2200])).
% 5.16/1.94  tff(c_2222, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_2170, c_2167, c_2215])).
% 5.16/1.94  tff(c_2224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_2222])).
% 5.16/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.94  
% 5.16/1.94  Inference rules
% 5.16/1.94  ----------------------
% 5.16/1.94  #Ref     : 0
% 5.16/1.94  #Sup     : 331
% 5.16/1.94  #Fact    : 0
% 5.16/1.94  #Define  : 0
% 5.16/1.94  #Split   : 24
% 5.16/1.94  #Chain   : 0
% 5.16/1.94  #Close   : 0
% 5.16/1.94  
% 5.16/1.94  Ordering : KBO
% 5.16/1.94  
% 5.16/1.94  Simplification rules
% 5.16/1.94  ----------------------
% 5.16/1.94  #Subsume      : 79
% 5.16/1.94  #Demod        : 761
% 5.16/1.94  #Tautology    : 138
% 5.16/1.94  #SimpNegUnit  : 86
% 5.16/1.94  #BackRed      : 0
% 5.16/1.94  
% 5.16/1.94  #Partial instantiations: 0
% 5.16/1.94  #Strategies tried      : 1
% 5.16/1.94  
% 5.16/1.94  Timing (in seconds)
% 5.16/1.94  ----------------------
% 5.16/1.95  Preprocessing        : 0.35
% 5.16/1.95  Parsing              : 0.17
% 5.16/1.95  CNF conversion       : 0.03
% 5.16/1.95  Main loop            : 0.76
% 5.16/1.95  Inferencing          : 0.31
% 5.16/1.95  Reduction            : 0.19
% 5.16/1.95  Demodulation         : 0.13
% 5.16/1.95  BG Simplification    : 0.05
% 5.16/1.95  Subsumption          : 0.18
% 5.16/1.95  Abstraction          : 0.03
% 5.16/1.95  MUC search           : 0.00
% 5.16/1.95  Cooper               : 0.00
% 5.16/1.95  Total                : 1.17
% 5.16/1.95  Index Insertion      : 0.00
% 5.16/1.95  Index Deletion       : 0.00
% 5.16/1.95  Index Matching       : 0.00
% 5.16/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
