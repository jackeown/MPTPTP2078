%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:18 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 269 expanded)
%              Number of leaves         :   27 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  203 (1008 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_49,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_34,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_145,plain,(
    ! [A_61,B_62] :
      ( '#skF_3'(A_61,B_62) != B_62
      | v3_tex_2(B_62,A_61)
      | ~ v2_tex_2(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_151,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148])).

tff(c_152,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_151])).

tff(c_160,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_38,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_48])).

tff(c_195,plain,(
    ! [B_71,A_72] :
      ( v2_tex_2(B_71,A_72)
      | ~ v1_zfmisc_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | v1_xboole_0(B_71)
      | ~ l1_pre_topc(A_72)
      | ~ v2_tdlat_3(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_201,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_205,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_50,c_201])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_32,c_160,c_205])).

tff(c_209,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_153,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(B_63,'#skF_3'(A_64,B_63))
      | v3_tex_2(B_63,A_64)
      | ~ v2_tex_2(B_63,A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_153])).

tff(c_158,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_155])).

tff(c_159,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_158])).

tff(c_218,plain,(
    r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_159])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40),B_41)
      | ~ r1_tarski(A_40,B_41)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [B_41,A_40] :
      ( ~ v1_xboole_0(B_41)
      | ~ r1_tarski(A_40,B_41)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_230,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_218,c_84])).

tff(c_239,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_230])).

tff(c_208,plain,(
    '#skF_3'('#skF_4','#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_24,plain,(
    ! [B_22,A_20] :
      ( B_22 = A_20
      | ~ r1_tarski(A_20,B_22)
      | ~ v1_zfmisc_1(B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_227,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_218,c_24])).

tff(c_236,plain,
    ( ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_208,c_227])).

tff(c_240,plain,(
    ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_236])).

tff(c_210,plain,(
    ! [A_73,B_74] :
      ( v2_tex_2('#skF_3'(A_73,B_74),A_73)
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_210])).

tff(c_215,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_209,c_212])).

tff(c_216,plain,(
    v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_215])).

tff(c_18,plain,(
    ! [A_10,B_16] :
      ( m1_subset_1('#skF_3'(A_10,B_16),k1_zfmisc_1(u1_struct_0(A_10)))
      | v3_tex_2(B_16,A_10)
      | ~ v2_tex_2(B_16,A_10)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_393,plain,(
    ! [B_97,A_98] :
      ( v1_zfmisc_1(B_97)
      | ~ v2_tex_2(B_97,A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(B_97)
      | ~ l1_pre_topc(A_98)
      | ~ v2_tdlat_3(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_591,plain,(
    ! [A_124,B_125] :
      ( v1_zfmisc_1('#skF_3'(A_124,B_125))
      | ~ v2_tex_2('#skF_3'(A_124,B_125),A_124)
      | v1_xboole_0('#skF_3'(A_124,B_125))
      | ~ v2_tdlat_3(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124)
      | v3_tex_2(B_125,A_124)
      | ~ v2_tex_2(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_18,c_393])).

tff(c_595,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_591])).

tff(c_599,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_209,c_38,c_36,c_595])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_40,c_239,c_240,c_599])).

tff(c_602,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_603,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_686,plain,(
    ! [B_154,A_155] :
      ( v2_tex_2(B_154,A_155)
      | ~ v3_tex_2(B_154,A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_689,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_686])).

tff(c_692,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_603,c_689])).

tff(c_719,plain,(
    ! [B_166,A_167] :
      ( v1_zfmisc_1(B_166)
      | ~ v2_tex_2(B_166,A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | v1_xboole_0(B_166)
      | ~ l1_pre_topc(A_167)
      | ~ v2_tdlat_3(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_722,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_719])).

tff(c_725,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_692,c_722])).

tff(c_727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_32,c_602,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.58  
% 2.96/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.59  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.96/1.59  
% 2.96/1.59  %Foreground sorts:
% 2.96/1.59  
% 2.96/1.59  
% 2.96/1.59  %Background operators:
% 2.96/1.59  
% 2.96/1.59  
% 2.96/1.59  %Foreground operators:
% 2.96/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.96/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.96/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.96/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.96/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.59  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.59  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.96/1.59  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.96/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.59  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.96/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.96/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.96/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.59  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.96/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.59  
% 2.96/1.60  tff(f_108, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 2.96/1.60  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.96/1.60  tff(f_88, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 2.96/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.96/1.60  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.96/1.60  tff(f_69, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.96/1.60  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_32, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_42, plain, (~v1_zfmisc_1('#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_49, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 2.96/1.60  tff(c_34, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_145, plain, (![A_61, B_62]: ('#skF_3'(A_61, B_62)!=B_62 | v3_tex_2(B_62, A_61) | ~v2_tex_2(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.60  tff(c_148, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_145])).
% 2.96/1.60  tff(c_151, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_148])).
% 2.96/1.60  tff(c_152, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_151])).
% 2.96/1.60  tff(c_160, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_152])).
% 2.96/1.60  tff(c_38, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_36, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_48, plain, (v3_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.96/1.60  tff(c_50, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_49, c_48])).
% 2.96/1.60  tff(c_195, plain, (![B_71, A_72]: (v2_tex_2(B_71, A_72) | ~v1_zfmisc_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | v1_xboole_0(B_71) | ~l1_pre_topc(A_72) | ~v2_tdlat_3(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.96/1.60  tff(c_201, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_195])).
% 2.96/1.60  tff(c_205, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_50, c_201])).
% 2.96/1.60  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_32, c_160, c_205])).
% 2.96/1.60  tff(c_209, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_152])).
% 2.96/1.60  tff(c_153, plain, (![B_63, A_64]: (r1_tarski(B_63, '#skF_3'(A_64, B_63)) | v3_tex_2(B_63, A_64) | ~v2_tex_2(B_63, A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.60  tff(c_155, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_153])).
% 2.96/1.60  tff(c_158, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_155])).
% 2.96/1.60  tff(c_159, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_158])).
% 2.96/1.60  tff(c_218, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_159])).
% 2.96/1.60  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.60  tff(c_70, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.60  tff(c_77, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40), B_41) | ~r1_tarski(A_40, B_41) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_4, c_70])).
% 2.96/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.60  tff(c_84, plain, (![B_41, A_40]: (~v1_xboole_0(B_41) | ~r1_tarski(A_40, B_41) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_77, c_2])).
% 2.96/1.60  tff(c_230, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_218, c_84])).
% 2.96/1.60  tff(c_239, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_32, c_230])).
% 2.96/1.60  tff(c_208, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_152])).
% 2.96/1.60  tff(c_24, plain, (![B_22, A_20]: (B_22=A_20 | ~r1_tarski(A_20, B_22) | ~v1_zfmisc_1(B_22) | v1_xboole_0(B_22) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.60  tff(c_227, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_218, c_24])).
% 2.96/1.60  tff(c_236, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_32, c_208, c_227])).
% 2.96/1.60  tff(c_240, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_239, c_236])).
% 2.96/1.60  tff(c_210, plain, (![A_73, B_74]: (v2_tex_2('#skF_3'(A_73, B_74), A_73) | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.60  tff(c_212, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_210])).
% 2.96/1.60  tff(c_215, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_209, c_212])).
% 2.96/1.60  tff(c_216, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_215])).
% 2.96/1.60  tff(c_18, plain, (![A_10, B_16]: (m1_subset_1('#skF_3'(A_10, B_16), k1_zfmisc_1(u1_struct_0(A_10))) | v3_tex_2(B_16, A_10) | ~v2_tex_2(B_16, A_10) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.60  tff(c_393, plain, (![B_97, A_98]: (v1_zfmisc_1(B_97) | ~v2_tex_2(B_97, A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(B_97) | ~l1_pre_topc(A_98) | ~v2_tdlat_3(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.96/1.60  tff(c_591, plain, (![A_124, B_125]: (v1_zfmisc_1('#skF_3'(A_124, B_125)) | ~v2_tex_2('#skF_3'(A_124, B_125), A_124) | v1_xboole_0('#skF_3'(A_124, B_125)) | ~v2_tdlat_3(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124) | v3_tex_2(B_125, A_124) | ~v2_tex_2(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_18, c_393])).
% 2.96/1.60  tff(c_595, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_216, c_591])).
% 2.96/1.60  tff(c_599, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_209, c_38, c_36, c_595])).
% 2.96/1.60  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_40, c_239, c_240, c_599])).
% 2.96/1.60  tff(c_602, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 2.96/1.60  tff(c_603, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.96/1.60  tff(c_686, plain, (![B_154, A_155]: (v2_tex_2(B_154, A_155) | ~v3_tex_2(B_154, A_155) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.60  tff(c_689, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_686])).
% 2.96/1.60  tff(c_692, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_603, c_689])).
% 2.96/1.60  tff(c_719, plain, (![B_166, A_167]: (v1_zfmisc_1(B_166) | ~v2_tex_2(B_166, A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | v1_xboole_0(B_166) | ~l1_pre_topc(A_167) | ~v2_tdlat_3(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.96/1.60  tff(c_722, plain, (v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_719])).
% 2.96/1.60  tff(c_725, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_692, c_722])).
% 2.96/1.60  tff(c_727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_32, c_602, c_725])).
% 2.96/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.60  
% 2.96/1.60  Inference rules
% 2.96/1.60  ----------------------
% 2.96/1.60  #Ref     : 0
% 2.96/1.60  #Sup     : 141
% 2.96/1.60  #Fact    : 0
% 2.96/1.60  #Define  : 0
% 2.96/1.60  #Split   : 7
% 2.96/1.60  #Chain   : 0
% 2.96/1.60  #Close   : 0
% 2.96/1.60  
% 2.96/1.60  Ordering : KBO
% 2.96/1.60  
% 2.96/1.60  Simplification rules
% 2.96/1.60  ----------------------
% 2.96/1.60  #Subsume      : 53
% 2.96/1.60  #Demod        : 74
% 2.96/1.60  #Tautology    : 22
% 2.96/1.60  #SimpNegUnit  : 26
% 2.96/1.60  #BackRed      : 0
% 2.96/1.60  
% 2.96/1.60  #Partial instantiations: 0
% 2.96/1.60  #Strategies tried      : 1
% 2.96/1.60  
% 2.96/1.60  Timing (in seconds)
% 2.96/1.60  ----------------------
% 2.96/1.61  Preprocessing        : 0.36
% 2.96/1.61  Parsing              : 0.21
% 2.96/1.61  CNF conversion       : 0.02
% 2.96/1.61  Main loop            : 0.37
% 2.96/1.61  Inferencing          : 0.14
% 2.96/1.61  Reduction            : 0.10
% 2.96/1.61  Demodulation         : 0.06
% 2.96/1.61  BG Simplification    : 0.02
% 2.96/1.61  Subsumption          : 0.09
% 2.96/1.61  Abstraction          : 0.01
% 2.96/1.61  MUC search           : 0.00
% 2.96/1.61  Cooper               : 0.00
% 2.96/1.61  Total                : 0.77
% 2.96/1.61  Index Insertion      : 0.00
% 2.96/1.61  Index Deletion       : 0.00
% 2.96/1.61  Index Matching       : 0.00
% 2.96/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
