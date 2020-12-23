%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1137+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 340 expanded)
%              Number of leaves         :   31 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 (1202 expanded)
%              Number of equality atoms :   14 (  72 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_orders_2(A,B,C)
                    & r1_orders_2(A,C,B) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_73,plain,(
    ! [A_71] :
      ( m1_subset_1(u1_orders_2(A_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(A_71))))
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_83,plain,(
    ! [A_71] :
      ( v1_relat_1(u1_orders_2(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_22,plain,(
    ! [B_26,C_28,A_22] :
      ( r2_hidden(k4_tarski(B_26,C_28),u1_orders_2(A_22))
      | ~ r1_orders_2(A_22,B_26,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(A_22))
      | ~ m1_subset_1(B_26,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_36,C_38,B_37] :
      ( m1_subset_1(A_36,C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_81,plain,(
    ! [A_36,A_71] :
      ( m1_subset_1(A_36,k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(A_71)))
      | ~ r2_hidden(A_36,u1_orders_2(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_73,c_34])).

tff(c_32,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_67,plain,(
    ! [A_64,C_65,B_66,D_67] :
      ( r2_hidden(A_64,C_65)
      | ~ r2_hidden(k4_tarski(A_64,B_66),k2_zfmisc_1(C_65,D_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_130,plain,(
    ! [A_94,C_95,D_96,B_97] :
      ( r2_hidden(A_94,C_95)
      | v1_xboole_0(k2_zfmisc_1(C_95,D_96))
      | ~ m1_subset_1(k4_tarski(A_94,B_97),k2_zfmisc_1(C_95,D_96)) ) ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_160,plain,(
    ! [A_114,A_115,B_116] :
      ( r2_hidden(A_114,u1_struct_0(A_115))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_115),u1_struct_0(A_115)))
      | ~ r2_hidden(k4_tarski(A_114,B_116),u1_orders_2(A_115))
      | ~ l1_orders_2(A_115) ) ),
    inference(resolution,[status(thm)],[c_81,c_130])).

tff(c_214,plain,(
    ! [B_137,A_138,C_139] :
      ( r2_hidden(B_137,u1_struct_0(A_138))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_138),u1_struct_0(A_138)))
      | ~ r1_orders_2(A_138,B_137,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0(A_138))
      | ~ m1_subset_1(B_137,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138) ) ),
    inference(resolution,[status(thm)],[c_22,c_160])).

tff(c_216,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_214])).

tff(c_221,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_216])).

tff(c_242,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_36,plain,(
    ! [C_41,B_40,A_39] :
      ( ~ v1_xboole_0(C_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    ! [A_71,A_39] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(A_71)))
      | ~ r2_hidden(A_39,u1_orders_2(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_73,c_36])).

tff(c_244,plain,(
    ! [A_39] :
      ( ~ r2_hidden(A_39,u1_orders_2('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_242,c_82])).

tff(c_248,plain,(
    ! [A_144] : ~ r2_hidden(A_144,u1_orders_2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_244])).

tff(c_268,plain,(
    ! [B_26,C_28] :
      ( ~ r1_orders_2('#skF_3',B_26,C_28)
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_26,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_248])).

tff(c_343,plain,(
    ! [B_157,C_158] :
      ( ~ r1_orders_2('#skF_3',B_157,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_268])).

tff(c_345,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_343])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_345])).

tff(c_353,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_10,plain,(
    ! [A_4,B_14] :
      ( r2_hidden(k4_tarski('#skF_1'(A_4,B_14),'#skF_2'(A_4,B_14)),A_4)
      | r4_relat_2(A_4,B_14)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    ! [B_58,D_59,A_60,C_61] :
      ( r2_hidden(B_58,D_59)
      | ~ r2_hidden(k4_tarski(A_60,B_58),k2_zfmisc_1(C_61,D_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,(
    ! [B_90,D_91,C_92,A_93] :
      ( r2_hidden(B_90,D_91)
      | v1_xboole_0(k2_zfmisc_1(C_92,D_91))
      | ~ m1_subset_1(k4_tarski(A_93,B_90),k2_zfmisc_1(C_92,D_91)) ) ),
    inference(resolution,[status(thm)],[c_32,c_61])).

tff(c_193,plain,(
    ! [B_121,A_122,A_123] :
      ( r2_hidden(B_121,u1_struct_0(A_122))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(A_122)))
      | ~ r2_hidden(k4_tarski(A_123,B_121),u1_orders_2(A_122))
      | ~ l1_orders_2(A_122) ) ),
    inference(resolution,[status(thm)],[c_81,c_124])).

tff(c_207,plain,(
    ! [A_122,B_14] :
      ( r2_hidden('#skF_2'(u1_orders_2(A_122),B_14),u1_struct_0(A_122))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | r4_relat_2(u1_orders_2(A_122),B_14)
      | ~ v1_relat_1(u1_orders_2(A_122)) ) ),
    inference(resolution,[status(thm)],[c_10,c_193])).

tff(c_352,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_176,plain,(
    ! [D_117,C_118,A_119,B_120] :
      ( D_117 = C_118
      | ~ r2_hidden(k4_tarski(D_117,C_118),A_119)
      | ~ r2_hidden(k4_tarski(C_118,D_117),A_119)
      | ~ r2_hidden(D_117,B_120)
      | ~ r2_hidden(C_118,B_120)
      | ~ r4_relat_2(A_119,B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_225,plain,(
    ! [D_140,C_141,B_142,B_143] :
      ( D_140 = C_141
      | ~ r2_hidden(k4_tarski(C_141,D_140),B_142)
      | ~ r2_hidden(D_140,B_143)
      | ~ r2_hidden(C_141,B_143)
      | ~ r4_relat_2(B_142,B_143)
      | ~ v1_relat_1(B_142)
      | v1_xboole_0(B_142)
      | ~ m1_subset_1(k4_tarski(D_140,C_141),B_142) ) ),
    inference(resolution,[status(thm)],[c_32,c_176])).

tff(c_384,plain,(
    ! [D_167,C_168,B_169,B_170] :
      ( D_167 = C_168
      | ~ r2_hidden(D_167,B_169)
      | ~ r2_hidden(C_168,B_169)
      | ~ r4_relat_2(B_170,B_169)
      | ~ v1_relat_1(B_170)
      | ~ m1_subset_1(k4_tarski(D_167,C_168),B_170)
      | v1_xboole_0(B_170)
      | ~ m1_subset_1(k4_tarski(C_168,D_167),B_170) ) ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_517,plain,(
    ! [C_177,B_178] :
      ( C_177 = '#skF_5'
      | ~ r2_hidden(C_177,u1_struct_0('#skF_3'))
      | ~ r4_relat_2(B_178,u1_struct_0('#skF_3'))
      | ~ v1_relat_1(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_5',C_177),B_178)
      | v1_xboole_0(B_178)
      | ~ m1_subset_1(k4_tarski(C_177,'#skF_5'),B_178) ) ),
    inference(resolution,[status(thm)],[c_352,c_384])).

tff(c_527,plain,(
    ! [B_14,B_178] :
      ( '#skF_2'(u1_orders_2('#skF_3'),B_14) = '#skF_5'
      | ~ r4_relat_2(B_178,u1_struct_0('#skF_3'))
      | ~ v1_relat_1(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_5','#skF_2'(u1_orders_2('#skF_3'),B_14)),B_178)
      | v1_xboole_0(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_2'(u1_orders_2('#skF_3'),B_14),'#skF_5'),B_178)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | r4_relat_2(u1_orders_2('#skF_3'),B_14)
      | ~ v1_relat_1(u1_orders_2('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_207,c_517])).

tff(c_565,plain,(
    ! [B_14,B_178] :
      ( '#skF_2'(u1_orders_2('#skF_3'),B_14) = '#skF_5'
      | ~ r4_relat_2(B_178,u1_struct_0('#skF_3'))
      | ~ v1_relat_1(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_5','#skF_2'(u1_orders_2('#skF_3'),B_14)),B_178)
      | v1_xboole_0(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_2'(u1_orders_2('#skF_3'),B_14),'#skF_5'),B_178)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))
      | r4_relat_2(u1_orders_2('#skF_3'),B_14)
      | ~ v1_relat_1(u1_orders_2('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_527])).

tff(c_566,plain,(
    ! [B_14,B_178] :
      ( '#skF_2'(u1_orders_2('#skF_3'),B_14) = '#skF_5'
      | ~ r4_relat_2(B_178,u1_struct_0('#skF_3'))
      | ~ v1_relat_1(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_5','#skF_2'(u1_orders_2('#skF_3'),B_14)),B_178)
      | v1_xboole_0(B_178)
      | ~ m1_subset_1(k4_tarski('#skF_2'(u1_orders_2('#skF_3'),B_14),'#skF_5'),B_178)
      | r4_relat_2(u1_orders_2('#skF_3'),B_14)
      | ~ v1_relat_1(u1_orders_2('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_565])).

tff(c_704,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_707,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_704])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_707])).

tff(c_713,plain,(
    v1_relat_1(u1_orders_2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_18,plain,(
    ! [A_21] :
      ( r4_relat_2(u1_orders_2(A_21),u1_struct_0(A_21))
      | ~ v5_orders_2(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_218,plain,
    ( r2_hidden('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_214])).

tff(c_224,plain,
    ( r2_hidden('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_218])).

tff(c_370,plain,(
    r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_224])).

tff(c_1037,plain,(
    ! [C_265,B_266,A_267,B_268] :
      ( C_265 = B_266
      | ~ r2_hidden(k4_tarski(C_265,B_266),u1_orders_2(A_267))
      | ~ r2_hidden(B_266,B_268)
      | ~ r2_hidden(C_265,B_268)
      | ~ r4_relat_2(u1_orders_2(A_267),B_268)
      | ~ v1_relat_1(u1_orders_2(A_267))
      | ~ r1_orders_2(A_267,B_266,C_265)
      | ~ m1_subset_1(C_265,u1_struct_0(A_267))
      | ~ m1_subset_1(B_266,u1_struct_0(A_267))
      | ~ l1_orders_2(A_267) ) ),
    inference(resolution,[status(thm)],[c_22,c_176])).

tff(c_1053,plain,(
    ! [C_269,B_270,B_271,A_272] :
      ( C_269 = B_270
      | ~ r2_hidden(C_269,B_271)
      | ~ r2_hidden(B_270,B_271)
      | ~ r4_relat_2(u1_orders_2(A_272),B_271)
      | ~ v1_relat_1(u1_orders_2(A_272))
      | ~ r1_orders_2(A_272,C_269,B_270)
      | ~ r1_orders_2(A_272,B_270,C_269)
      | ~ m1_subset_1(C_269,u1_struct_0(A_272))
      | ~ m1_subset_1(B_270,u1_struct_0(A_272))
      | ~ l1_orders_2(A_272) ) ),
    inference(resolution,[status(thm)],[c_22,c_1037])).

tff(c_1099,plain,(
    ! [B_273,A_274] :
      ( B_273 = '#skF_4'
      | ~ r2_hidden(B_273,u1_struct_0('#skF_3'))
      | ~ r4_relat_2(u1_orders_2(A_274),u1_struct_0('#skF_3'))
      | ~ v1_relat_1(u1_orders_2(A_274))
      | ~ r1_orders_2(A_274,'#skF_4',B_273)
      | ~ r1_orders_2(A_274,B_273,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_274))
      | ~ m1_subset_1(B_273,u1_struct_0(A_274))
      | ~ l1_orders_2(A_274) ) ),
    inference(resolution,[status(thm)],[c_370,c_1053])).

tff(c_1103,plain,(
    ! [A_274] :
      ( '#skF_5' = '#skF_4'
      | ~ r4_relat_2(u1_orders_2(A_274),u1_struct_0('#skF_3'))
      | ~ v1_relat_1(u1_orders_2(A_274))
      | ~ r1_orders_2(A_274,'#skF_4','#skF_5')
      | ~ r1_orders_2(A_274,'#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_274))
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_274))
      | ~ l1_orders_2(A_274) ) ),
    inference(resolution,[status(thm)],[c_352,c_1099])).

tff(c_1160,plain,(
    ! [A_275] :
      ( ~ r4_relat_2(u1_orders_2(A_275),u1_struct_0('#skF_3'))
      | ~ v1_relat_1(u1_orders_2(A_275))
      | ~ r1_orders_2(A_275,'#skF_4','#skF_5')
      | ~ r1_orders_2(A_275,'#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_275))
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_275))
      | ~ l1_orders_2(A_275) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1103])).

tff(c_1167,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_3'))
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ v5_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1160])).

tff(c_1172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_44,c_46,c_40,c_42,c_713,c_1167])).

%------------------------------------------------------------------------------
