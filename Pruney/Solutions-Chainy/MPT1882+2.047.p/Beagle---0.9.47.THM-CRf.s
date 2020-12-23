%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 291 expanded)
%              Number of leaves         :   32 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 (1136 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( C != k1_xboole_0
                    & v3_pre_topc(C,A)
                    & r1_xboole_0(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

tff(f_75,axiom,(
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

tff(f_126,axiom,(
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

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v2_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( v3_pre_topc(B,A)
                & B != k1_xboole_0
                & B != u1_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_67,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_532,plain,(
    ! [B_111,A_112] :
      ( r1_xboole_0(B_111,'#skF_1'(A_112,B_111))
      | v1_tops_1(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_539,plain,
    ( r1_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5'))
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_532])).

tff(c_544,plain,
    ( r1_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5'))
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_539])).

tff(c_545,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_165,plain,(
    ! [A_63,B_64] :
      ( '#skF_2'(A_63,B_64) != B_64
      | v3_tex_2(B_64,A_63)
      | ~ v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_175,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_165])).

tff(c_180,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_175])).

tff(c_181,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_180])).

tff(c_182,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_66,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_66])).

tff(c_481,plain,(
    ! [B_105,A_106] :
      ( v2_tex_2(B_105,A_106)
      | ~ v1_zfmisc_1(B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | v1_xboole_0(B_105)
      | ~ l1_pre_topc(A_106)
      | ~ v2_tdlat_3(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_497,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_481])).

tff(c_504,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_68,c_497])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_182,c_504])).

tff(c_508,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_701,plain,(
    ! [B_139,A_140] :
      ( v3_tex_2(B_139,A_140)
      | ~ v2_tex_2(B_139,A_140)
      | ~ v1_tops_1(B_139,A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_714,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_701])).

tff(c_720,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_545,c_508,c_714])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_67,c_720])).

tff(c_723,plain,(
    r1_xboole_0('#skF_5','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski(B_2,A_1)
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_727,plain,
    ( ~ r1_tarski('#skF_5','#skF_1'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_723,c_2])).

tff(c_730,plain,(
    ~ r1_tarski('#skF_5','#skF_1'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_727])).

tff(c_724,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_105,plain,(
    ! [A_52,B_53] :
      ( '#skF_1'(A_52,B_53) != k1_xboole_0
      | v1_tops_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,
    ( '#skF_1'('#skF_4','#skF_5') != k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_105])).

tff(c_120,plain,
    ( '#skF_1'('#skF_4','#skF_5') != k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_115])).

tff(c_121,plain,(
    '#skF_1'('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_731,plain,(
    ! [A_141,B_142] :
      ( v3_pre_topc('#skF_1'(A_141,B_142),A_141)
      | v1_tops_1(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_738,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_731])).

tff(c_743,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_738])).

tff(c_744,plain,(
    v3_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_743])).

tff(c_814,plain,(
    ! [A_161,B_162] :
      ( m1_subset_1('#skF_1'(A_161,B_162),k1_zfmisc_1(u1_struct_0(A_161)))
      | v1_tops_1(B_162,A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_25,B_28] :
      ( u1_struct_0(A_25) = B_28
      | k1_xboole_0 = B_28
      | ~ v3_pre_topc(B_28,A_25)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ v2_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1258,plain,(
    ! [A_222,B_223] :
      ( u1_struct_0(A_222) = '#skF_1'(A_222,B_223)
      | '#skF_1'(A_222,B_223) = k1_xboole_0
      | ~ v3_pre_topc('#skF_1'(A_222,B_223),A_222)
      | ~ v2_tdlat_3(A_222)
      | v1_tops_1(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_814,c_30])).

tff(c_1268,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_5')
    | '#skF_1'('#skF_4','#skF_5') = k1_xboole_0
    | ~ v2_tdlat_3('#skF_4')
    | v1_tops_1('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_744,c_1258])).

tff(c_1275,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_5')
    | '#skF_1'('#skF_4','#skF_5') = k1_xboole_0
    | v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_48,c_54,c_1268])).

tff(c_1276,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_121,c_1275])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_1279,plain,(
    r1_tarski('#skF_5','#skF_1'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_78])).

tff(c_1282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_1279])).

tff(c_1283,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1331,plain,(
    ! [A_232,B_233] :
      ( '#skF_2'(A_232,B_233) != B_233
      | v3_tex_2(B_233,A_232)
      | ~ v2_tex_2(B_233,A_232)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1341,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1331])).

tff(c_1346,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1341])).

tff(c_1347,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1346])).

tff(c_1348,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1347])).

tff(c_1565,plain,(
    ! [B_267,A_268] :
      ( v2_tex_2(B_267,A_268)
      | ~ v1_zfmisc_1(B_267)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_268)))
      | v1_xboole_0(B_267)
      | ~ l1_pre_topc(A_268)
      | ~ v2_tdlat_3(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1578,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1565])).

tff(c_1584,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_68,c_1578])).

tff(c_1586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_1348,c_1584])).

tff(c_1588,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1347])).

tff(c_1924,plain,(
    ! [B_312,A_313] :
      ( v3_tex_2(B_312,A_313)
      | ~ v2_tex_2(B_312,A_313)
      | ~ v1_tops_1(B_312,A_313)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1940,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1924])).

tff(c_1947,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1283,c_1588,c_1940])).

tff(c_1949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_67,c_1947])).

tff(c_1950,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1951,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1974,plain,(
    ! [B_325,A_326] :
      ( v2_tex_2(B_325,A_326)
      | ~ v3_tex_2(B_325,A_326)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1984,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1974])).

tff(c_1989,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1951,c_1984])).

tff(c_2359,plain,(
    ! [B_380,A_381] :
      ( v1_zfmisc_1(B_380)
      | ~ v2_tex_2(B_380,A_381)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_381)))
      | v1_xboole_0(B_380)
      | ~ l1_pre_topc(A_381)
      | ~ v2_tdlat_3(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2375,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2359])).

tff(c_2382,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1989,c_2375])).

tff(c_2384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_1950,c_2382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.79  
% 4.65/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.79  %$ v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.65/1.79  
% 4.65/1.79  %Foreground sorts:
% 4.65/1.79  
% 4.65/1.79  
% 4.65/1.79  %Background operators:
% 4.65/1.79  
% 4.65/1.79  
% 4.65/1.79  %Foreground operators:
% 4.65/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.65/1.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.65/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.65/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.65/1.79  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.65/1.79  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.65/1.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.65/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.65/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.65/1.79  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.65/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.65/1.79  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.65/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.65/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.65/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.65/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.65/1.79  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.65/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.79  
% 4.65/1.81  tff(f_162, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 4.65/1.81  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(C = k1_xboole_0) & v3_pre_topc(C, A)) & r1_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tops_1)).
% 4.65/1.81  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.65/1.81  tff(f_126, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 4.65/1.81  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.65/1.81  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.65/1.81  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v2_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(B, A) & ~(B = k1_xboole_0)) & ~(B = u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tdlat_3)).
% 4.65/1.81  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.65/1.81  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_60, plain, (~v1_zfmisc_1('#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_67, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.65/1.81  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_532, plain, (![B_111, A_112]: (r1_xboole_0(B_111, '#skF_1'(A_112, B_111)) | v1_tops_1(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.65/1.81  tff(c_539, plain, (r1_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5')) | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_532])).
% 4.65/1.81  tff(c_544, plain, (r1_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5')) | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_539])).
% 4.65/1.81  tff(c_545, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_544])).
% 4.65/1.81  tff(c_165, plain, (![A_63, B_64]: ('#skF_2'(A_63, B_64)!=B_64 | v3_tex_2(B_64, A_63) | ~v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.65/1.81  tff(c_175, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_165])).
% 4.65/1.81  tff(c_180, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_175])).
% 4.65/1.81  tff(c_181, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_67, c_180])).
% 4.65/1.81  tff(c_182, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_181])).
% 4.65/1.81  tff(c_54, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_66, plain, (v3_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.65/1.81  tff(c_68, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_67, c_66])).
% 4.65/1.81  tff(c_481, plain, (![B_105, A_106]: (v2_tex_2(B_105, A_106) | ~v1_zfmisc_1(B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | v1_xboole_0(B_105) | ~l1_pre_topc(A_106) | ~v2_tdlat_3(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.65/1.81  tff(c_497, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_481])).
% 4.65/1.81  tff(c_504, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_68, c_497])).
% 4.65/1.81  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_182, c_504])).
% 4.65/1.81  tff(c_508, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_181])).
% 4.65/1.81  tff(c_701, plain, (![B_139, A_140]: (v3_tex_2(B_139, A_140) | ~v2_tex_2(B_139, A_140) | ~v1_tops_1(B_139, A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.65/1.81  tff(c_714, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_701])).
% 4.65/1.81  tff(c_720, plain, (v3_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_545, c_508, c_714])).
% 4.65/1.81  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_67, c_720])).
% 4.65/1.81  tff(c_723, plain, (r1_xboole_0('#skF_5', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_544])).
% 4.65/1.81  tff(c_2, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski(B_2, A_1) | v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.65/1.81  tff(c_727, plain, (~r1_tarski('#skF_5', '#skF_1'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_723, c_2])).
% 4.65/1.81  tff(c_730, plain, (~r1_tarski('#skF_5', '#skF_1'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_727])).
% 4.65/1.81  tff(c_724, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_544])).
% 4.65/1.81  tff(c_105, plain, (![A_52, B_53]: ('#skF_1'(A_52, B_53)!=k1_xboole_0 | v1_tops_1(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.65/1.81  tff(c_115, plain, ('#skF_1'('#skF_4', '#skF_5')!=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_105])).
% 4.65/1.81  tff(c_120, plain, ('#skF_1'('#skF_4', '#skF_5')!=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_115])).
% 4.65/1.81  tff(c_121, plain, ('#skF_1'('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_120])).
% 4.65/1.81  tff(c_731, plain, (![A_141, B_142]: (v3_pre_topc('#skF_1'(A_141, B_142), A_141) | v1_tops_1(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.65/1.81  tff(c_738, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_731])).
% 4.65/1.81  tff(c_743, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_738])).
% 4.65/1.81  tff(c_744, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_724, c_743])).
% 4.65/1.81  tff(c_814, plain, (![A_161, B_162]: (m1_subset_1('#skF_1'(A_161, B_162), k1_zfmisc_1(u1_struct_0(A_161))) | v1_tops_1(B_162, A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.65/1.81  tff(c_30, plain, (![A_25, B_28]: (u1_struct_0(A_25)=B_28 | k1_xboole_0=B_28 | ~v3_pre_topc(B_28, A_25) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_25))) | ~v2_tdlat_3(A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.65/1.81  tff(c_1258, plain, (![A_222, B_223]: (u1_struct_0(A_222)='#skF_1'(A_222, B_223) | '#skF_1'(A_222, B_223)=k1_xboole_0 | ~v3_pre_topc('#skF_1'(A_222, B_223), A_222) | ~v2_tdlat_3(A_222) | v1_tops_1(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222))), inference(resolution, [status(thm)], [c_814, c_30])).
% 4.65/1.81  tff(c_1268, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_5') | '#skF_1'('#skF_4', '#skF_5')=k1_xboole_0 | ~v2_tdlat_3('#skF_4') | v1_tops_1('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_744, c_1258])).
% 4.65/1.81  tff(c_1275, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_5') | '#skF_1'('#skF_4', '#skF_5')=k1_xboole_0 | v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_48, c_54, c_1268])).
% 4.65/1.81  tff(c_1276, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_724, c_121, c_1275])).
% 4.65/1.81  tff(c_70, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.81  tff(c_78, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_70])).
% 4.65/1.81  tff(c_1279, plain, (r1_tarski('#skF_5', '#skF_1'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_78])).
% 4.65/1.81  tff(c_1282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_730, c_1279])).
% 4.65/1.81  tff(c_1283, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_120])).
% 4.65/1.81  tff(c_1331, plain, (![A_232, B_233]: ('#skF_2'(A_232, B_233)!=B_233 | v3_tex_2(B_233, A_232) | ~v2_tex_2(B_233, A_232) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.65/1.81  tff(c_1341, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1331])).
% 4.65/1.81  tff(c_1346, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1341])).
% 4.65/1.81  tff(c_1347, plain, ('#skF_2'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_67, c_1346])).
% 4.65/1.81  tff(c_1348, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1347])).
% 4.65/1.81  tff(c_1565, plain, (![B_267, A_268]: (v2_tex_2(B_267, A_268) | ~v1_zfmisc_1(B_267) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_268))) | v1_xboole_0(B_267) | ~l1_pre_topc(A_268) | ~v2_tdlat_3(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.65/1.81  tff(c_1578, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1565])).
% 4.65/1.81  tff(c_1584, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_68, c_1578])).
% 4.65/1.81  tff(c_1586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_1348, c_1584])).
% 4.65/1.81  tff(c_1588, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1347])).
% 4.65/1.81  tff(c_1924, plain, (![B_312, A_313]: (v3_tex_2(B_312, A_313) | ~v2_tex_2(B_312, A_313) | ~v1_tops_1(B_312, A_313) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.65/1.81  tff(c_1940, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1924])).
% 4.65/1.81  tff(c_1947, plain, (v3_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1283, c_1588, c_1940])).
% 4.65/1.81  tff(c_1949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_67, c_1947])).
% 4.65/1.81  tff(c_1950, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 4.65/1.81  tff(c_1951, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 4.65/1.81  tff(c_1974, plain, (![B_325, A_326]: (v2_tex_2(B_325, A_326) | ~v3_tex_2(B_325, A_326) | ~m1_subset_1(B_325, k1_zfmisc_1(u1_struct_0(A_326))) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.65/1.81  tff(c_1984, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1974])).
% 4.65/1.81  tff(c_1989, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1951, c_1984])).
% 4.65/1.81  tff(c_2359, plain, (![B_380, A_381]: (v1_zfmisc_1(B_380) | ~v2_tex_2(B_380, A_381) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_381))) | v1_xboole_0(B_380) | ~l1_pre_topc(A_381) | ~v2_tdlat_3(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.65/1.81  tff(c_2375, plain, (v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2359])).
% 4.65/1.81  tff(c_2382, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1989, c_2375])).
% 4.65/1.81  tff(c_2384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_1950, c_2382])).
% 4.65/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.81  
% 4.65/1.81  Inference rules
% 4.65/1.81  ----------------------
% 4.65/1.81  #Ref     : 0
% 4.65/1.81  #Sup     : 482
% 4.65/1.81  #Fact    : 0
% 4.65/1.81  #Define  : 0
% 4.65/1.81  #Split   : 18
% 4.65/1.81  #Chain   : 0
% 4.65/1.81  #Close   : 0
% 4.65/1.81  
% 4.65/1.81  Ordering : KBO
% 4.65/1.81  
% 4.65/1.81  Simplification rules
% 4.65/1.81  ----------------------
% 4.65/1.81  #Subsume      : 76
% 4.65/1.81  #Demod        : 313
% 4.65/1.81  #Tautology    : 71
% 4.65/1.81  #SimpNegUnit  : 63
% 4.65/1.81  #BackRed      : 4
% 4.65/1.81  
% 4.65/1.81  #Partial instantiations: 0
% 4.65/1.81  #Strategies tried      : 1
% 4.65/1.81  
% 4.65/1.81  Timing (in seconds)
% 4.65/1.81  ----------------------
% 4.65/1.81  Preprocessing        : 0.33
% 4.65/1.81  Parsing              : 0.17
% 4.65/1.81  CNF conversion       : 0.02
% 4.65/1.81  Main loop            : 0.71
% 4.65/1.81  Inferencing          : 0.29
% 4.65/1.81  Reduction            : 0.19
% 4.79/1.81  Demodulation         : 0.12
% 4.79/1.81  BG Simplification    : 0.03
% 4.79/1.81  Subsumption          : 0.13
% 4.79/1.81  Abstraction          : 0.04
% 4.79/1.81  MUC search           : 0.00
% 4.79/1.81  Cooper               : 0.00
% 4.79/1.81  Total                : 1.08
% 4.79/1.81  Index Insertion      : 0.00
% 4.79/1.81  Index Deletion       : 0.00
% 4.79/1.81  Index Matching       : 0.00
% 4.79/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
