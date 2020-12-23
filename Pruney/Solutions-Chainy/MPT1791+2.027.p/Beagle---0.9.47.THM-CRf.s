%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 179 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  198 ( 575 expanded)
%              Number of equality atoms :   41 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(f_98,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_37,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_43,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_28])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    ! [B_21,A_22] :
      ( v3_pre_topc(B_21,A_22)
      | ~ r2_hidden(B_21,u1_pre_topc(A_22))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_66])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_156,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,u1_pre_topc(A_30))
      | k5_tmap_1(A_30,B_29) != u1_pre_topc(A_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_168,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_156])).

tff(c_173,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_168])).

tff(c_174,plain,(
    k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_67,c_173])).

tff(c_97,plain,(
    ! [A_25,B_26] :
      ( u1_pre_topc(k6_tmap_1(A_25,B_26)) = k5_tmap_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_97])).

tff(c_110,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_106])).

tff(c_111,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_110])).

tff(c_6,plain,(
    ! [A_4] :
      ( v3_pre_topc('#skF_1'(A_4),A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1'(A_4),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [B_18,A_19] :
      ( r2_hidden(B_18,u1_pre_topc(A_19))
      | ~ v3_pre_topc(B_18,A_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),u1_pre_topc(A_4))
      | ~ v3_pre_topc('#skF_1'(A_4),A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_198,plain,(
    ! [A_34,B_35] :
      ( k5_tmap_1(A_34,B_35) = u1_pre_topc(A_34)
      | ~ r2_hidden(B_35,u1_pre_topc(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_236,plain,(
    ! [A_37] :
      ( k5_tmap_1(A_37,'#skF_1'(A_37)) = u1_pre_topc(A_37)
      | ~ r2_hidden('#skF_1'(A_37),u1_pre_topc(A_37))
      | v2_struct_0(A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_8,c_198])).

tff(c_254,plain,(
    ! [A_38] :
      ( k5_tmap_1(A_38,'#skF_1'(A_38)) = u1_pre_topc(A_38)
      | v2_struct_0(A_38)
      | ~ v3_pre_topc('#skF_1'(A_38),A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_51,c_236])).

tff(c_259,plain,(
    ! [A_39] :
      ( k5_tmap_1(A_39,'#skF_1'(A_39)) = u1_pre_topc(A_39)
      | v2_struct_0(A_39)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_183,plain,(
    ! [A_32,B_33] :
      ( g1_pre_topc(u1_struct_0(A_32),k5_tmap_1(A_32,B_33)) = k6_tmap_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_193,plain,(
    ! [A_4] :
      ( g1_pre_topc(u1_struct_0(A_4),k5_tmap_1(A_4,'#skF_1'(A_4))) = k6_tmap_1(A_4,'#skF_1'(A_4))
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_272,plain,(
    ! [A_40] :
      ( g1_pre_topc(u1_struct_0(A_40),u1_pre_topc(A_40)) = k6_tmap_1(A_40,'#skF_1'(A_40))
      | v2_struct_0(A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_193])).

tff(c_278,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_37])).

tff(c_299,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_24,c_22,c_278])).

tff(c_300,plain,(
    k6_tmap_1('#skF_2','#skF_1'('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_299])).

tff(c_107,plain,(
    ! [A_4] :
      ( u1_pre_topc(k6_tmap_1(A_4,'#skF_1'(A_4))) = k5_tmap_1(A_4,'#skF_1'(A_4))
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_310,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2')) = u1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_107])).

tff(c_317,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_111,c_310])).

tff(c_318,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_317])).

tff(c_258,plain,(
    ! [A_4] :
      ( k5_tmap_1(A_4,'#skF_1'(A_4)) = u1_pre_topc(A_4)
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_327,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_258])).

tff(c_337,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_327])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_174,c_337])).

tff(c_340,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_342,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_342])).

tff(c_345,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_348,plain,(
    ! [B_41,A_42] :
      ( r2_hidden(B_41,u1_pre_topc(A_42))
      | ~ v3_pre_topc(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_354,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_348])).

tff(c_358,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_340,c_354])).

tff(c_488,plain,(
    ! [A_55,B_56] :
      ( k5_tmap_1(A_55,B_56) = u1_pre_topc(A_55)
      | ~ r2_hidden(B_56,u1_pre_topc(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_500,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_488])).

tff(c_505,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_358,c_500])).

tff(c_506,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_505])).

tff(c_523,plain,(
    ! [A_57,B_58] :
      ( g1_pre_topc(u1_struct_0(A_57),k5_tmap_1(A_57,B_58)) = k6_tmap_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_531,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_523])).

tff(c_536,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_506,c_531])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_345,c_536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:01:00 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.42  
% 2.40/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.42  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.40/1.42  
% 2.40/1.42  %Foreground sorts:
% 2.40/1.42  
% 2.40/1.42  
% 2.40/1.42  %Background operators:
% 2.40/1.42  
% 2.40/1.42  
% 2.40/1.42  %Foreground operators:
% 2.40/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.40/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.40/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.42  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.40/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.40/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.42  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.40/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.42  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.40/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.42  
% 2.66/1.44  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 2.66/1.44  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.66/1.44  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.66/1.44  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.66/1.44  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_tops_1)).
% 2.66/1.44  tff(f_55, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.66/1.44  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.44  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.44  tff(c_37, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.66/1.44  tff(c_28, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.44  tff(c_43, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_28])).
% 2.66/1.44  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.44  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.44  tff(c_56, plain, (![B_21, A_22]: (v3_pre_topc(B_21, A_22) | ~r2_hidden(B_21, u1_pre_topc(A_22)) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.44  tff(c_62, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_56])).
% 2.66/1.44  tff(c_66, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62])).
% 2.66/1.44  tff(c_67, plain, (~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_43, c_66])).
% 2.66/1.44  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.44  tff(c_156, plain, (![B_29, A_30]: (r2_hidden(B_29, u1_pre_topc(A_30)) | k5_tmap_1(A_30, B_29)!=u1_pre_topc(A_30) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.44  tff(c_168, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_156])).
% 2.66/1.44  tff(c_173, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_168])).
% 2.66/1.44  tff(c_174, plain, (k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_67, c_173])).
% 2.66/1.44  tff(c_97, plain, (![A_25, B_26]: (u1_pre_topc(k6_tmap_1(A_25, B_26))=k5_tmap_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.44  tff(c_106, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_97])).
% 2.66/1.44  tff(c_110, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_106])).
% 2.66/1.44  tff(c_111, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_110])).
% 2.66/1.44  tff(c_6, plain, (![A_4]: (v3_pre_topc('#skF_1'(A_4), A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.44  tff(c_8, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.44  tff(c_44, plain, (![B_18, A_19]: (r2_hidden(B_18, u1_pre_topc(A_19)) | ~v3_pre_topc(B_18, A_19) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.44  tff(c_51, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), u1_pre_topc(A_4)) | ~v3_pre_topc('#skF_1'(A_4), A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_44])).
% 2.66/1.44  tff(c_198, plain, (![A_34, B_35]: (k5_tmap_1(A_34, B_35)=u1_pre_topc(A_34) | ~r2_hidden(B_35, u1_pre_topc(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.44  tff(c_236, plain, (![A_37]: (k5_tmap_1(A_37, '#skF_1'(A_37))=u1_pre_topc(A_37) | ~r2_hidden('#skF_1'(A_37), u1_pre_topc(A_37)) | v2_struct_0(A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(resolution, [status(thm)], [c_8, c_198])).
% 2.66/1.44  tff(c_254, plain, (![A_38]: (k5_tmap_1(A_38, '#skF_1'(A_38))=u1_pre_topc(A_38) | v2_struct_0(A_38) | ~v3_pre_topc('#skF_1'(A_38), A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(resolution, [status(thm)], [c_51, c_236])).
% 2.66/1.44  tff(c_259, plain, (![A_39]: (k5_tmap_1(A_39, '#skF_1'(A_39))=u1_pre_topc(A_39) | v2_struct_0(A_39) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39))), inference(resolution, [status(thm)], [c_6, c_254])).
% 2.66/1.44  tff(c_183, plain, (![A_32, B_33]: (g1_pre_topc(u1_struct_0(A_32), k5_tmap_1(A_32, B_33))=k6_tmap_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.44  tff(c_193, plain, (![A_4]: (g1_pre_topc(u1_struct_0(A_4), k5_tmap_1(A_4, '#skF_1'(A_4)))=k6_tmap_1(A_4, '#skF_1'(A_4)) | v2_struct_0(A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_183])).
% 2.66/1.44  tff(c_272, plain, (![A_40]: (g1_pre_topc(u1_struct_0(A_40), u1_pre_topc(A_40))=k6_tmap_1(A_40, '#skF_1'(A_40)) | v2_struct_0(A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(superposition, [status(thm), theory('equality')], [c_259, c_193])).
% 2.66/1.44  tff(c_278, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_272, c_37])).
% 2.66/1.44  tff(c_299, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_24, c_22, c_278])).
% 2.66/1.44  tff(c_300, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_299])).
% 2.66/1.44  tff(c_107, plain, (![A_4]: (u1_pre_topc(k6_tmap_1(A_4, '#skF_1'(A_4)))=k5_tmap_1(A_4, '#skF_1'(A_4)) | v2_struct_0(A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.66/1.44  tff(c_310, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2'))=u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_300, c_107])).
% 2.66/1.44  tff(c_317, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_111, c_310])).
% 2.66/1.44  tff(c_318, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_317])).
% 2.66/1.44  tff(c_258, plain, (![A_4]: (k5_tmap_1(A_4, '#skF_1'(A_4))=u1_pre_topc(A_4) | v2_struct_0(A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(resolution, [status(thm)], [c_6, c_254])).
% 2.66/1.44  tff(c_327, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_318, c_258])).
% 2.66/1.44  tff(c_337, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_327])).
% 2.66/1.44  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_174, c_337])).
% 2.66/1.44  tff(c_340, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.66/1.44  tff(c_342, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 2.66/1.44  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_340, c_342])).
% 2.66/1.44  tff(c_345, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.66/1.44  tff(c_348, plain, (![B_41, A_42]: (r2_hidden(B_41, u1_pre_topc(A_42)) | ~v3_pre_topc(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.44  tff(c_354, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_348])).
% 2.66/1.44  tff(c_358, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_340, c_354])).
% 2.66/1.44  tff(c_488, plain, (![A_55, B_56]: (k5_tmap_1(A_55, B_56)=u1_pre_topc(A_55) | ~r2_hidden(B_56, u1_pre_topc(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.66/1.44  tff(c_500, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_488])).
% 2.66/1.44  tff(c_505, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_358, c_500])).
% 2.66/1.44  tff(c_506, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_505])).
% 2.66/1.44  tff(c_523, plain, (![A_57, B_58]: (g1_pre_topc(u1_struct_0(A_57), k5_tmap_1(A_57, B_58))=k6_tmap_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.44  tff(c_531, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_523])).
% 2.66/1.44  tff(c_536, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_506, c_531])).
% 2.66/1.44  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_345, c_536])).
% 2.66/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.44  
% 2.66/1.44  Inference rules
% 2.66/1.44  ----------------------
% 2.66/1.44  #Ref     : 0
% 2.66/1.44  #Sup     : 123
% 2.66/1.44  #Fact    : 0
% 2.66/1.44  #Define  : 0
% 2.66/1.44  #Split   : 6
% 2.66/1.44  #Chain   : 0
% 2.66/1.44  #Close   : 0
% 2.66/1.44  
% 2.66/1.44  Ordering : KBO
% 2.66/1.44  
% 2.66/1.44  Simplification rules
% 2.66/1.44  ----------------------
% 2.66/1.44  #Subsume      : 25
% 2.66/1.44  #Demod        : 74
% 2.66/1.44  #Tautology    : 41
% 2.66/1.44  #SimpNegUnit  : 16
% 2.66/1.44  #BackRed      : 1
% 2.66/1.44  
% 2.66/1.44  #Partial instantiations: 0
% 2.66/1.44  #Strategies tried      : 1
% 2.66/1.44  
% 2.66/1.44  Timing (in seconds)
% 2.66/1.44  ----------------------
% 2.66/1.44  Preprocessing        : 0.31
% 2.66/1.44  Parsing              : 0.17
% 2.66/1.44  CNF conversion       : 0.02
% 2.66/1.44  Main loop            : 0.29
% 2.66/1.44  Inferencing          : 0.11
% 2.66/1.44  Reduction            : 0.09
% 2.66/1.44  Demodulation         : 0.06
% 2.66/1.44  BG Simplification    : 0.02
% 2.66/1.44  Subsumption          : 0.05
% 2.66/1.44  Abstraction          : 0.02
% 2.66/1.44  MUC search           : 0.00
% 2.66/1.44  Cooper               : 0.00
% 2.66/1.44  Total                : 0.63
% 2.66/1.44  Index Insertion      : 0.00
% 2.66/1.44  Index Deletion       : 0.00
% 2.66/1.44  Index Matching       : 0.00
% 2.66/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
