%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1881+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:37 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 308 expanded)
%              Number of leaves         :   23 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  206 ( 929 expanded)
%              Number of equality atoms :   23 (  93 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_55,axiom,(
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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_430,plain,(
    ! [B_74] :
      ( ~ v1_subset_1(B_74,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_434,plain,(
    ! [B_19] :
      ( ~ v1_subset_1(B_19,B_19)
      | ~ r1_tarski(B_19,B_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_430])).

tff(c_437,plain,(
    ! [B_19] : ~ v1_subset_1(B_19,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_434])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_493,plain,(
    ! [A_86] :
      ( v2_tex_2(u1_struct_0(A_86),A_86)
      | ~ v1_tdlat_3(A_86)
      | ~ m1_subset_1(u1_struct_0(A_86),k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_496,plain,(
    ! [A_86] :
      ( v2_tex_2(u1_struct_0(A_86),A_86)
      | ~ v1_tdlat_3(A_86)
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86)
      | ~ r1_tarski(u1_struct_0(A_86),u1_struct_0(A_86)) ) ),
    inference(resolution,[status(thm)],[c_30,c_493])).

tff(c_499,plain,(
    ! [A_86] :
      ( v2_tex_2(u1_struct_0(A_86),A_86)
      | ~ v1_tdlat_3(A_86)
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_496])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_51,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_42])).

tff(c_82,plain,(
    ! [B_30,A_31] :
      ( v1_subset_1(B_30,A_31)
      | B_30 = A_31
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_92,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_88])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_32])).

tff(c_163,plain,(
    ! [A_41] :
      ( v2_tex_2(u1_struct_0(A_41),A_41)
      | ~ v1_tdlat_3(A_41)
      | ~ m1_subset_1(u1_struct_0(A_41),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_166,plain,
    ( v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_163])).

tff(c_174,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95,c_92,c_36,c_92,c_166])).

tff(c_175,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_174])).

tff(c_220,plain,(
    ! [A_45,B_46] :
      ( '#skF_1'(A_45,B_46) != B_46
      | v3_tex_2(B_46,A_45)
      | ~ v2_tex_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_223,plain,(
    ! [B_46] :
      ( '#skF_1'('#skF_2',B_46) != B_46
      | v3_tex_2(B_46,'#skF_2')
      | ~ v2_tex_2(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_220])).

tff(c_231,plain,(
    ! [B_47] :
      ( '#skF_1'('#skF_2',B_47) != B_47
      | v3_tex_2(B_47,'#skF_2')
      | ~ v2_tex_2(B_47,'#skF_2')
      | ~ m1_subset_1(B_47,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_223])).

tff(c_234,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_231])).

tff(c_241,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_234])).

tff(c_242,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_241])).

tff(c_352,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1('#skF_1'(A_66,B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | v3_tex_2(B_67,A_66)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_371,plain,(
    ! [B_67] :
      ( m1_subset_1('#skF_1'('#skF_2',B_67),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_67,'#skF_2')
      | ~ v2_tex_2(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_352])).

tff(c_380,plain,(
    ! [B_68] :
      ( m1_subset_1('#skF_1'('#skF_2',B_68),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_68,'#skF_2')
      | ~ v2_tex_2(B_68,'#skF_2')
      | ~ m1_subset_1(B_68,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_92,c_371])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_397,plain,(
    ! [B_69] :
      ( r1_tarski('#skF_1'('#skF_2',B_69),'#skF_3')
      | v3_tex_2(B_69,'#skF_2')
      | ~ v2_tex_2(B_69,'#skF_2')
      | ~ m1_subset_1(B_69,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_380,c_28])).

tff(c_262,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,'#skF_1'(A_50,B_49))
      | v3_tex_2(B_49,A_50)
      | ~ v2_tex_2(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_305,plain,(
    ! [A_56,A_57] :
      ( r1_tarski(A_56,'#skF_1'(A_57,A_56))
      | v3_tex_2(A_56,A_57)
      | ~ v2_tex_2(A_56,A_57)
      | ~ l1_pre_topc(A_57)
      | ~ r1_tarski(A_56,u1_struct_0(A_57)) ) ),
    inference(resolution,[status(thm)],[c_30,c_262])).

tff(c_307,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,'#skF_1'('#skF_2',A_56))
      | v3_tex_2(A_56,'#skF_2')
      | ~ v2_tex_2(A_56,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_56,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_305])).

tff(c_314,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_1'('#skF_2',A_58))
      | v3_tex_2(A_58,'#skF_2')
      | ~ v2_tex_2(A_58,'#skF_2')
      | ~ r1_tarski(A_58,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_307])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_317,plain,(
    ! [A_58] :
      ( '#skF_1'('#skF_2',A_58) = A_58
      | ~ r1_tarski('#skF_1'('#skF_2',A_58),A_58)
      | v3_tex_2(A_58,'#skF_2')
      | ~ v2_tex_2(A_58,'#skF_2')
      | ~ r1_tarski(A_58,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_314,c_2])).

tff(c_401,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_397,c_317])).

tff(c_413,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_175,c_6,c_401])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_242,c_413])).

tff(c_416,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_420,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_424,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_420])).

tff(c_616,plain,(
    ! [C_109,B_110,A_111] :
      ( C_109 = B_110
      | ~ r1_tarski(B_110,C_109)
      | ~ v2_tex_2(C_109,A_111)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ v3_tex_2(B_110,A_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_627,plain,(
    ! [A_111] :
      ( u1_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_111)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ v3_tex_2('#skF_3',A_111)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_424,c_616])).

tff(c_632,plain,(
    ! [A_114] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_114)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tex_2('#skF_3',A_114)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(splitLeft,[status(thm)],[c_627])).

tff(c_637,plain,(
    ! [A_115] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_115)
      | ~ v3_tex_2('#skF_3',A_115)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(A_115)) ) ),
    inference(resolution,[status(thm)],[c_30,c_632])).

tff(c_641,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_637])).

tff(c_644,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_416,c_641])).

tff(c_647,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_499,c_644])).

tff(c_650,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_647])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_650])).

tff(c_653,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_627])).

tff(c_439,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_444,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_424,c_439])).

tff(c_449,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_654,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_449])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_654])).

tff(c_661,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_417,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_664,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_417])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_664])).

%------------------------------------------------------------------------------
