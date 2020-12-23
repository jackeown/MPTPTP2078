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
% DateTime   : Thu Dec  3 10:30:14 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 505 expanded)
%              Number of leaves         :   31 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  234 (1880 expanded)
%              Number of equality atoms :   19 ( 132 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_83,axiom,(
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

tff(f_115,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C] :
                  ( r2_hidden(C,B)
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_mcart_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_62,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_63,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_164,plain,(
    ! [A_62,B_63] :
      ( '#skF_2'(A_62,B_63) != B_63
      | v3_tex_2(B_63,A_62)
      | ~ v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_171,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_164])).

tff(c_175,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_171])).

tff(c_176,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_175])).

tff(c_188,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_305,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ v1_zfmisc_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | v1_xboole_0(B_83)
      | ~ l1_pre_topc(A_84)
      | ~ v2_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_315,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_305])).

tff(c_320,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_62,c_315])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_188,c_320])).

tff(c_323,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_zfmisc_1(A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_324,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_345,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,'#skF_2'(A_89,B_88))
      | v3_tex_2(B_88,A_89)
      | ~ v2_tex_2(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_350,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_345])).

tff(c_354,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_324,c_350])).

tff(c_355,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_354])).

tff(c_34,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_358,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_355,c_34])).

tff(c_366,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_323,c_358])).

tff(c_717,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_730,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_717])).

tff(c_18,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    ! [B_46,A_47,A_48] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_47,A_48)
      | ~ r1_tarski(A_48,B_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_104,plain,(
    ! [B_46,A_9] :
      ( ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_9,B_46)
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_367,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_355,c_104])).

tff(c_371,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_372,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_177,plain,(
    ! [A_64,B_65] :
      ( v2_tex_2('#skF_2'(A_64,B_65),A_64)
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_182,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_177])).

tff(c_186,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_182])).

tff(c_187,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_186])).

tff(c_326,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_187])).

tff(c_428,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1('#skF_2'(A_100,B_101),k1_zfmisc_1(u1_struct_0(A_100)))
      | v3_tex_2(B_101,A_100)
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [B_31,A_29] :
      ( v1_zfmisc_1(B_31)
      | ~ v2_tex_2(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_29)
      | ~ v2_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_693,plain,(
    ! [A_138,B_139] :
      ( v1_zfmisc_1('#skF_2'(A_138,B_139))
      | ~ v2_tex_2('#skF_2'(A_138,B_139),A_138)
      | v1_xboole_0('#skF_2'(A_138,B_139))
      | ~ v2_tdlat_3(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138)
      | v3_tex_2(B_139,A_138)
      | ~ v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_428,c_38])).

tff(c_699,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_326,c_693])).

tff(c_704,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_324,c_48,c_46,c_699])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_371,c_372,c_704])).

tff(c_707,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_371])).

tff(c_716,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_716])).

tff(c_733,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_715,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | ~ r1_tarski(A_50,B_49)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_113,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_767,plain,(
    ! [B_143] :
      ( ~ v1_xboole_0(B_143)
      | B_143 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_113])).

tff(c_770,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_733,c_767])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_770])).

tff(c_775,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_775])).

tff(c_780,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_779,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_862,plain,(
    ! [B_166,A_167] :
      ( v2_tex_2(B_166,A_167)
      | ~ v3_tex_2(B_166,A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_869,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_862])).

tff(c_873,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_779,c_869])).

tff(c_937,plain,(
    ! [B_182,A_183] :
      ( v1_zfmisc_1(B_182)
      | ~ v2_tex_2(B_182,A_183)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | v1_xboole_0(B_182)
      | ~ l1_pre_topc(A_183)
      | ~ v2_tdlat_3(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_944,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_937])).

tff(c_948,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_873,c_944])).

tff(c_950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_780,c_948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.53  
% 3.55/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.53  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.55/1.53  
% 3.55/1.53  %Foreground sorts:
% 3.55/1.53  
% 3.55/1.53  
% 3.55/1.53  %Background operators:
% 3.55/1.53  
% 3.55/1.53  
% 3.55/1.53  %Foreground operators:
% 3.55/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.55/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.55/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.55/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.53  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.55/1.53  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.55/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.55/1.53  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.55/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.55/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.53  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.55/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.53  
% 3.55/1.55  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.55/1.55  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.55/1.55  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.55/1.55  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.55/1.55  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.55/1.55  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C]: (r2_hidden(C, B) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_mcart_1)).
% 3.55/1.55  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.55/1.55  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.55/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.55  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_62, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 3.55/1.55  tff(c_52, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_63, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.55/1.55  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_164, plain, (![A_62, B_63]: ('#skF_2'(A_62, B_63)!=B_63 | v3_tex_2(B_63, A_62) | ~v2_tex_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.55  tff(c_171, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_164])).
% 3.55/1.55  tff(c_175, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_171])).
% 3.55/1.55  tff(c_176, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_175])).
% 3.55/1.55  tff(c_188, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_176])).
% 3.55/1.55  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_46, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.55/1.55  tff(c_305, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~v1_zfmisc_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | v1_xboole_0(B_83) | ~l1_pre_topc(A_84) | ~v2_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.55/1.55  tff(c_315, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_305])).
% 3.55/1.55  tff(c_320, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_62, c_315])).
% 3.55/1.55  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_188, c_320])).
% 3.55/1.55  tff(c_323, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_176])).
% 3.55/1.55  tff(c_8, plain, (![A_3]: (v1_zfmisc_1(A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.55  tff(c_324, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_176])).
% 3.55/1.55  tff(c_345, plain, (![B_88, A_89]: (r1_tarski(B_88, '#skF_2'(A_89, B_88)) | v3_tex_2(B_88, A_89) | ~v2_tex_2(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.55  tff(c_350, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_345])).
% 3.55/1.55  tff(c_354, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_324, c_350])).
% 3.55/1.55  tff(c_355, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_63, c_354])).
% 3.55/1.55  tff(c_34, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.55/1.55  tff(c_358, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_355, c_34])).
% 3.55/1.55  tff(c_366, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_323, c_358])).
% 3.55/1.55  tff(c_717, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_366])).
% 3.55/1.55  tff(c_730, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_717])).
% 3.55/1.55  tff(c_18, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.55  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.55/1.55  tff(c_93, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.55  tff(c_101, plain, (![B_46, A_47, A_48]: (~v1_xboole_0(B_46) | ~r2_hidden(A_47, A_48) | ~r1_tarski(A_48, B_46))), inference(resolution, [status(thm)], [c_12, c_93])).
% 3.55/1.55  tff(c_104, plain, (![B_46, A_9]: (~v1_xboole_0(B_46) | ~r1_tarski(A_9, B_46) | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_18, c_101])).
% 3.55/1.55  tff(c_367, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_355, c_104])).
% 3.55/1.55  tff(c_371, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_367])).
% 3.55/1.55  tff(c_372, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_366])).
% 3.55/1.55  tff(c_177, plain, (![A_64, B_65]: (v2_tex_2('#skF_2'(A_64, B_65), A_64) | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.55  tff(c_182, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_177])).
% 3.55/1.55  tff(c_186, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_182])).
% 3.55/1.55  tff(c_187, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_186])).
% 3.55/1.55  tff(c_326, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_187])).
% 3.55/1.55  tff(c_428, plain, (![A_100, B_101]: (m1_subset_1('#skF_2'(A_100, B_101), k1_zfmisc_1(u1_struct_0(A_100))) | v3_tex_2(B_101, A_100) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.55  tff(c_38, plain, (![B_31, A_29]: (v1_zfmisc_1(B_31) | ~v2_tex_2(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_29) | ~v2_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.55/1.55  tff(c_693, plain, (![A_138, B_139]: (v1_zfmisc_1('#skF_2'(A_138, B_139)) | ~v2_tex_2('#skF_2'(A_138, B_139), A_138) | v1_xboole_0('#skF_2'(A_138, B_139)) | ~v2_tdlat_3(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138) | v3_tex_2(B_139, A_138) | ~v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_428, c_38])).
% 3.55/1.55  tff(c_699, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_326, c_693])).
% 3.55/1.55  tff(c_704, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_324, c_48, c_46, c_699])).
% 3.55/1.55  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_371, c_372, c_704])).
% 3.55/1.55  tff(c_707, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_366])).
% 3.55/1.55  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_707, c_371])).
% 3.55/1.55  tff(c_716, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_367])).
% 3.55/1.55  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_730, c_716])).
% 3.55/1.55  tff(c_733, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_366])).
% 3.55/1.55  tff(c_715, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_367])).
% 3.55/1.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.55  tff(c_105, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | ~r1_tarski(A_50, B_49) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_18, c_101])).
% 3.55/1.55  tff(c_113, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_6, c_105])).
% 3.55/1.55  tff(c_767, plain, (![B_143]: (~v1_xboole_0(B_143) | B_143='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_715, c_113])).
% 3.55/1.55  tff(c_770, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_733, c_767])).
% 3.55/1.55  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_770])).
% 3.55/1.55  tff(c_775, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.55/1.55  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_775])).
% 3.55/1.55  tff(c_780, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 3.55/1.55  tff(c_779, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 3.55/1.55  tff(c_862, plain, (![B_166, A_167]: (v2_tex_2(B_166, A_167) | ~v3_tex_2(B_166, A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.55  tff(c_869, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_862])).
% 3.55/1.55  tff(c_873, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_779, c_869])).
% 3.55/1.55  tff(c_937, plain, (![B_182, A_183]: (v1_zfmisc_1(B_182) | ~v2_tex_2(B_182, A_183) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_183))) | v1_xboole_0(B_182) | ~l1_pre_topc(A_183) | ~v2_tdlat_3(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.55/1.55  tff(c_944, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_937])).
% 3.55/1.55  tff(c_948, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_873, c_944])).
% 3.55/1.55  tff(c_950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_780, c_948])).
% 3.55/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.55  
% 3.55/1.55  Inference rules
% 3.55/1.55  ----------------------
% 3.55/1.55  #Ref     : 0
% 3.55/1.55  #Sup     : 166
% 3.55/1.55  #Fact    : 0
% 3.55/1.55  #Define  : 0
% 3.55/1.55  #Split   : 14
% 3.55/1.55  #Chain   : 0
% 3.55/1.55  #Close   : 0
% 3.55/1.55  
% 3.55/1.55  Ordering : KBO
% 3.55/1.55  
% 3.55/1.55  Simplification rules
% 3.55/1.55  ----------------------
% 3.55/1.55  #Subsume      : 36
% 3.55/1.55  #Demod        : 114
% 3.55/1.55  #Tautology    : 33
% 3.55/1.55  #SimpNegUnit  : 30
% 3.55/1.55  #BackRed      : 10
% 3.55/1.55  
% 3.55/1.55  #Partial instantiations: 0
% 3.55/1.55  #Strategies tried      : 1
% 3.55/1.55  
% 3.55/1.55  Timing (in seconds)
% 3.55/1.55  ----------------------
% 3.55/1.55  Preprocessing        : 0.30
% 3.55/1.55  Parsing              : 0.16
% 3.55/1.55  CNF conversion       : 0.02
% 3.55/1.55  Main loop            : 0.46
% 3.55/1.55  Inferencing          : 0.17
% 3.55/1.55  Reduction            : 0.12
% 3.55/1.55  Demodulation         : 0.08
% 3.55/1.55  BG Simplification    : 0.02
% 3.55/1.55  Subsumption          : 0.11
% 3.55/1.55  Abstraction          : 0.02
% 3.55/1.55  MUC search           : 0.00
% 3.55/1.55  Cooper               : 0.00
% 3.55/1.55  Total                : 0.80
% 3.55/1.55  Index Insertion      : 0.00
% 3.55/1.55  Index Deletion       : 0.00
% 3.55/1.55  Index Matching       : 0.00
% 3.55/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
