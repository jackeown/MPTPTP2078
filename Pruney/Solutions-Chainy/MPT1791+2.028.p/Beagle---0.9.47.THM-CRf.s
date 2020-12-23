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
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 175 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 ( 566 expanded)
%              Number of equality atoms :   42 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_59,plain,(
    ! [B_22,A_23] :
      ( v3_pre_topc(B_22,A_23)
      | ~ r2_hidden(B_22,u1_pre_topc(A_23))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_69,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_65])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_69])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_243,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,u1_pre_topc(A_39))
      | k5_tmap_1(A_39,B_38) != u1_pre_topc(A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_255,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_243])).

tff(c_260,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_255])).

tff(c_261,plain,(
    k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_70,c_260])).

tff(c_83,plain,(
    ! [A_26,B_27] :
      ( u1_pre_topc(k6_tmap_1(A_26,B_27)) = k5_tmap_1(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_89,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_93,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_89])).

tff(c_94,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_93])).

tff(c_8,plain,(
    ! [A_4] :
      ( v3_pre_topc('#skF_1'(A_4),A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1'(A_4),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [B_19,A_20] :
      ( r2_hidden(B_19,u1_pre_topc(A_20))
      | ~ v3_pre_topc(B_19,A_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),u1_pre_topc(A_4))
      | ~ v3_pre_topc('#skF_1'(A_4),A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_159,plain,(
    ! [A_30,B_31] :
      ( k5_tmap_1(A_30,B_31) = u1_pre_topc(A_30)
      | ~ r2_hidden(B_31,u1_pre_topc(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_178,plain,(
    ! [A_32] :
      ( k5_tmap_1(A_32,'#skF_1'(A_32)) = u1_pre_topc(A_32)
      | ~ r2_hidden('#skF_1'(A_32),u1_pre_topc(A_32))
      | v2_struct_0(A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_190,plain,(
    ! [A_33] :
      ( k5_tmap_1(A_33,'#skF_1'(A_33)) = u1_pre_topc(A_33)
      | v2_struct_0(A_33)
      | ~ v3_pre_topc('#skF_1'(A_33),A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_54,c_178])).

tff(c_194,plain,(
    ! [A_4] :
      ( k5_tmap_1(A_4,'#skF_1'(A_4)) = u1_pre_topc(A_4)
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_195,plain,(
    ! [A_34,B_35] :
      ( g1_pre_topc(u1_struct_0(A_34),k5_tmap_1(A_34,B_35)) = k6_tmap_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_223,plain,(
    ! [A_37] :
      ( g1_pre_topc(u1_struct_0(A_37),k5_tmap_1(A_37,'#skF_1'(A_37))) = k6_tmap_1(A_37,'#skF_1'(A_37))
      | v2_struct_0(A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_271,plain,(
    ! [A_41] :
      ( g1_pre_topc(u1_struct_0(A_41),u1_pre_topc(A_41)) = k6_tmap_1(A_41,'#skF_1'(A_41))
      | v2_struct_0(A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_223])).

tff(c_277,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_40])).

tff(c_298,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_26,c_24,c_277])).

tff(c_299,plain,(
    k6_tmap_1('#skF_2','#skF_1'('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_298])).

tff(c_90,plain,(
    ! [A_4] :
      ( u1_pre_topc(k6_tmap_1(A_4,'#skF_1'(A_4))) = k5_tmap_1(A_4,'#skF_1'(A_4))
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_83])).

tff(c_309,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2')) = u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_90])).

tff(c_316,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_94,c_309])).

tff(c_317,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_316])).

tff(c_329,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_194])).

tff(c_339,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_329])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_261,c_339])).

tff(c_343,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_342,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_357,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,u1_pre_topc(A_45))
      | ~ v3_pre_topc(B_44,A_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_363,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_357])).

tff(c_367,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_342,c_363])).

tff(c_491,plain,(
    ! [A_56,B_57] :
      ( k5_tmap_1(A_56,B_57) = u1_pre_topc(A_56)
      | ~ r2_hidden(B_57,u1_pre_topc(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_503,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_491])).

tff(c_508,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_367,c_503])).

tff(c_509,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_508])).

tff(c_457,plain,(
    ! [A_53,B_54] :
      ( g1_pre_topc(u1_struct_0(A_53),k5_tmap_1(A_53,B_54)) = k6_tmap_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_465,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_457])).

tff(c_470,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_465])).

tff(c_471,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_470])).

tff(c_510,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_471])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:07:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.43  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.49/1.43  
% 2.49/1.43  %Foreground sorts:
% 2.49/1.43  
% 2.49/1.43  
% 2.49/1.43  %Background operators:
% 2.49/1.43  
% 2.49/1.43  
% 2.49/1.43  %Foreground operators:
% 2.49/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.43  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.49/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.43  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.49/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.49/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.43  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.43  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.49/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.43  
% 2.84/1.44  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.84/1.44  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.84/1.44  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.84/1.44  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.84/1.44  tff(f_45, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_tops_1)).
% 2.84/1.44  tff(f_57, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.84/1.44  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.84/1.44  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.84/1.44  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.84/1.44  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.84/1.44  tff(c_46, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 2.84/1.44  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.84/1.44  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.84/1.44  tff(c_59, plain, (![B_22, A_23]: (v3_pre_topc(B_22, A_23) | ~r2_hidden(B_22, u1_pre_topc(A_23)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.84/1.44  tff(c_65, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_59])).
% 2.84/1.44  tff(c_69, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_65])).
% 2.84/1.44  tff(c_70, plain, (~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_69])).
% 2.84/1.44  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.84/1.44  tff(c_243, plain, (![B_38, A_39]: (r2_hidden(B_38, u1_pre_topc(A_39)) | k5_tmap_1(A_39, B_38)!=u1_pre_topc(A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.44  tff(c_255, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_243])).
% 2.84/1.44  tff(c_260, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_255])).
% 2.84/1.45  tff(c_261, plain, (k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_70, c_260])).
% 2.84/1.45  tff(c_83, plain, (![A_26, B_27]: (u1_pre_topc(k6_tmap_1(A_26, B_27))=k5_tmap_1(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.45  tff(c_89, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_83])).
% 2.84/1.45  tff(c_93, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_89])).
% 2.84/1.45  tff(c_94, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_93])).
% 2.84/1.45  tff(c_8, plain, (![A_4]: (v3_pre_topc('#skF_1'(A_4), A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.84/1.45  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.84/1.45  tff(c_47, plain, (![B_19, A_20]: (r2_hidden(B_19, u1_pre_topc(A_20)) | ~v3_pre_topc(B_19, A_20) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.84/1.45  tff(c_54, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), u1_pre_topc(A_4)) | ~v3_pre_topc('#skF_1'(A_4), A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_10, c_47])).
% 2.84/1.45  tff(c_159, plain, (![A_30, B_31]: (k5_tmap_1(A_30, B_31)=u1_pre_topc(A_30) | ~r2_hidden(B_31, u1_pre_topc(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.45  tff(c_178, plain, (![A_32]: (k5_tmap_1(A_32, '#skF_1'(A_32))=u1_pre_topc(A_32) | ~r2_hidden('#skF_1'(A_32), u1_pre_topc(A_32)) | v2_struct_0(A_32) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(resolution, [status(thm)], [c_10, c_159])).
% 2.84/1.45  tff(c_190, plain, (![A_33]: (k5_tmap_1(A_33, '#skF_1'(A_33))=u1_pre_topc(A_33) | v2_struct_0(A_33) | ~v3_pre_topc('#skF_1'(A_33), A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(resolution, [status(thm)], [c_54, c_178])).
% 2.84/1.45  tff(c_194, plain, (![A_4]: (k5_tmap_1(A_4, '#skF_1'(A_4))=u1_pre_topc(A_4) | v2_struct_0(A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_190])).
% 2.84/1.45  tff(c_195, plain, (![A_34, B_35]: (g1_pre_topc(u1_struct_0(A_34), k5_tmap_1(A_34, B_35))=k6_tmap_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_223, plain, (![A_37]: (g1_pre_topc(u1_struct_0(A_37), k5_tmap_1(A_37, '#skF_1'(A_37)))=k6_tmap_1(A_37, '#skF_1'(A_37)) | v2_struct_0(A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(resolution, [status(thm)], [c_10, c_195])).
% 2.84/1.45  tff(c_271, plain, (![A_41]: (g1_pre_topc(u1_struct_0(A_41), u1_pre_topc(A_41))=k6_tmap_1(A_41, '#skF_1'(A_41)) | v2_struct_0(A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(superposition, [status(thm), theory('equality')], [c_194, c_223])).
% 2.84/1.45  tff(c_277, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_271, c_40])).
% 2.84/1.45  tff(c_298, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_26, c_24, c_277])).
% 2.84/1.45  tff(c_299, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_298])).
% 2.84/1.45  tff(c_90, plain, (![A_4]: (u1_pre_topc(k6_tmap_1(A_4, '#skF_1'(A_4)))=k5_tmap_1(A_4, '#skF_1'(A_4)) | v2_struct_0(A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_10, c_83])).
% 2.84/1.45  tff(c_309, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2'))=u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_299, c_90])).
% 2.84/1.45  tff(c_316, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_94, c_309])).
% 2.84/1.45  tff(c_317, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_316])).
% 2.84/1.45  tff(c_329, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_317, c_194])).
% 2.84/1.45  tff(c_339, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_329])).
% 2.84/1.45  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_261, c_339])).
% 2.84/1.45  tff(c_343, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.84/1.45  tff(c_342, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.84/1.45  tff(c_357, plain, (![B_44, A_45]: (r2_hidden(B_44, u1_pre_topc(A_45)) | ~v3_pre_topc(B_44, A_45) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.84/1.45  tff(c_363, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_357])).
% 2.84/1.45  tff(c_367, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_342, c_363])).
% 2.84/1.45  tff(c_491, plain, (![A_56, B_57]: (k5_tmap_1(A_56, B_57)=u1_pre_topc(A_56) | ~r2_hidden(B_57, u1_pre_topc(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.84/1.45  tff(c_503, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_491])).
% 2.84/1.45  tff(c_508, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_367, c_503])).
% 2.84/1.45  tff(c_509, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_28, c_508])).
% 2.84/1.45  tff(c_457, plain, (![A_53, B_54]: (g1_pre_topc(u1_struct_0(A_53), k5_tmap_1(A_53, B_54))=k6_tmap_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.45  tff(c_465, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_457])).
% 2.84/1.45  tff(c_470, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_465])).
% 2.84/1.45  tff(c_471, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_470])).
% 2.84/1.45  tff(c_510, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_471])).
% 2.84/1.45  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_510])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 116
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 4
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 22
% 2.84/1.45  #Demod        : 68
% 2.84/1.45  #Tautology    : 39
% 2.84/1.45  #SimpNegUnit  : 17
% 2.84/1.45  #BackRed      : 2
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.32
% 2.84/1.45  Parsing              : 0.18
% 2.84/1.45  CNF conversion       : 0.02
% 2.84/1.45  Main loop            : 0.30
% 2.84/1.45  Inferencing          : 0.11
% 2.84/1.45  Reduction            : 0.09
% 2.84/1.45  Demodulation         : 0.07
% 2.84/1.45  BG Simplification    : 0.02
% 2.84/1.45  Subsumption          : 0.05
% 2.84/1.45  Abstraction          : 0.02
% 2.84/1.45  MUC search           : 0.00
% 2.84/1.45  Cooper               : 0.00
% 2.84/1.45  Total                : 0.66
% 2.84/1.45  Index Insertion      : 0.00
% 2.84/1.45  Index Deletion       : 0.00
% 2.84/1.45  Index Matching       : 0.00
% 2.84/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
