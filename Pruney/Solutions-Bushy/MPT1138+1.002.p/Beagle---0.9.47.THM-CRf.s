%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1138+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 16.18s
% Output     : CNFRefutation 16.32s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 480 expanded)
%              Number of leaves         :   33 ( 184 expanded)
%              Depth                    :   19
%              Number of atoms          :  302 (1783 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                     => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(c_42,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    ! [B_33,C_35,A_29] :
      ( r2_hidden(k4_tarski(B_33,C_35),u1_orders_2(A_29))
      | ~ r1_orders_2(A_29,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_139,plain,(
    ! [A_97] :
      ( m1_subset_1(u1_orders_2(A_97),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(A_97))))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_45,C_47,B_46] :
      ( m1_subset_1(A_45,C_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_147,plain,(
    ! [A_45,A_97] :
      ( m1_subset_1(A_45,k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(A_97)))
      | ~ r2_hidden(A_45,u1_orders_2(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_139,c_38])).

tff(c_36,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_86,plain,(
    ! [A_82,C_83,B_84,D_85] :
      ( r2_hidden(A_82,C_83)
      | ~ r2_hidden(k4_tarski(A_82,B_84),k2_zfmisc_1(C_83,D_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_266,plain,(
    ! [A_128,C_129,D_130,B_131] :
      ( r2_hidden(A_128,C_129)
      | v1_xboole_0(k2_zfmisc_1(C_129,D_130))
      | ~ m1_subset_1(k4_tarski(A_128,B_131),k2_zfmisc_1(C_129,D_130)) ) ),
    inference(resolution,[status(thm)],[c_36,c_86])).

tff(c_804,plain,(
    ! [A_214,A_215,B_216] :
      ( r2_hidden(A_214,u1_struct_0(A_215))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_215),u1_struct_0(A_215)))
      | ~ r2_hidden(k4_tarski(A_214,B_216),u1_orders_2(A_215))
      | ~ l1_orders_2(A_215) ) ),
    inference(resolution,[status(thm)],[c_147,c_266])).

tff(c_1623,plain,(
    ! [B_338,A_339,C_340] :
      ( r2_hidden(B_338,u1_struct_0(A_339))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_339),u1_struct_0(A_339)))
      | ~ r1_orders_2(A_339,B_338,C_340)
      | ~ m1_subset_1(C_340,u1_struct_0(A_339))
      | ~ m1_subset_1(B_338,u1_struct_0(A_339))
      | ~ l1_orders_2(A_339) ) ),
    inference(resolution,[status(thm)],[c_24,c_804])).

tff(c_1629,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1623])).

tff(c_1636,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1629])).

tff(c_1640,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1636])).

tff(c_40,plain,(
    ! [C_50,B_49,A_48] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_148,plain,(
    ! [A_97,A_48] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(A_97)))
      | ~ r2_hidden(A_48,u1_orders_2(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_139,c_40])).

tff(c_1642,plain,(
    ! [A_48] :
      ( ~ r2_hidden(A_48,u1_orders_2('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1640,c_148])).

tff(c_1646,plain,(
    ! [A_341] : ~ r2_hidden(A_341,u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1642])).

tff(c_1650,plain,(
    ! [B_33,C_35] :
      ( ~ r1_orders_2('#skF_4',B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_1646])).

tff(c_1805,plain,(
    ! [B_350,C_351] :
      ( ~ r1_orders_2('#skF_4',B_350,C_351)
      | ~ m1_subset_1(C_351,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_350,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1650])).

tff(c_1813,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_1805])).

tff(c_1825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1813])).

tff(c_1826,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1636])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_149,plain,(
    ! [A_97] :
      ( v1_relat_1(u1_orders_2(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_1827,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1636])).

tff(c_12,plain,(
    ! [A_5,B_19] :
      ( r2_hidden(k4_tarski('#skF_2'(A_5,B_19),'#skF_3'(A_5,B_19)),A_5)
      | r8_relat_2(A_5,B_19)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_817,plain,(
    ! [A_215,B_19] :
      ( r2_hidden('#skF_2'(u1_orders_2(A_215),B_19),u1_struct_0(A_215))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_215),u1_struct_0(A_215)))
      | ~ l1_orders_2(A_215)
      | r8_relat_2(u1_orders_2(A_215),B_19)
      | ~ v1_relat_1(u1_orders_2(A_215)) ) ),
    inference(resolution,[status(thm)],[c_12,c_804])).

tff(c_71,plain,(
    ! [B_74,D_75,A_76,C_77] :
      ( r2_hidden(B_74,D_75)
      | ~ r2_hidden(k4_tarski(A_76,B_74),k2_zfmisc_1(C_77,D_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_236,plain,(
    ! [B_121,D_122,C_123,A_124] :
      ( r2_hidden(B_121,D_122)
      | v1_xboole_0(k2_zfmisc_1(C_123,D_122))
      | ~ m1_subset_1(k4_tarski(A_124,B_121),k2_zfmisc_1(C_123,D_122)) ) ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_742,plain,(
    ! [B_208,A_209,A_210] :
      ( r2_hidden(B_208,u1_struct_0(A_209))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_209),u1_struct_0(A_209)))
      | ~ r2_hidden(k4_tarski(A_210,B_208),u1_orders_2(A_209))
      | ~ l1_orders_2(A_209) ) ),
    inference(resolution,[status(thm)],[c_147,c_236])).

tff(c_1863,plain,(
    ! [C_357,A_358,B_359] :
      ( r2_hidden(C_357,u1_struct_0(A_358))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_358),u1_struct_0(A_358)))
      | ~ r1_orders_2(A_358,B_359,C_357)
      | ~ m1_subset_1(C_357,u1_struct_0(A_358))
      | ~ m1_subset_1(B_359,u1_struct_0(A_358))
      | ~ l1_orders_2(A_358) ) ),
    inference(resolution,[status(thm)],[c_24,c_742])).

tff(c_1871,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1863])).

tff(c_1880,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_1871])).

tff(c_1881,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1827,c_1880])).

tff(c_462,plain,(
    ! [B_159,D_160,A_158,E_157,C_156] :
      ( r2_hidden(k4_tarski(C_156,E_157),A_158)
      | ~ r2_hidden(k4_tarski(D_160,E_157),A_158)
      | ~ r2_hidden(k4_tarski(C_156,D_160),A_158)
      | ~ r2_hidden(E_157,B_159)
      | ~ r2_hidden(D_160,B_159)
      | ~ r2_hidden(C_156,B_159)
      | ~ r8_relat_2(A_158,B_159)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_923,plain,(
    ! [C_245,E_242,B_243,B_244,D_241] :
      ( r2_hidden(k4_tarski(C_245,E_242),B_244)
      | ~ r2_hidden(k4_tarski(C_245,D_241),B_244)
      | ~ r2_hidden(E_242,B_243)
      | ~ r2_hidden(D_241,B_243)
      | ~ r2_hidden(C_245,B_243)
      | ~ r8_relat_2(B_244,B_243)
      | ~ v1_relat_1(B_244)
      | v1_xboole_0(B_244)
      | ~ m1_subset_1(k4_tarski(D_241,E_242),B_244) ) ),
    inference(resolution,[status(thm)],[c_36,c_462])).

tff(c_1920,plain,(
    ! [B_374,E_372,D_371,C_370,B_373] :
      ( r2_hidden(k4_tarski(C_370,E_372),B_374)
      | ~ r2_hidden(E_372,B_373)
      | ~ r2_hidden(D_371,B_373)
      | ~ r2_hidden(C_370,B_373)
      | ~ r8_relat_2(B_374,B_373)
      | ~ v1_relat_1(B_374)
      | ~ m1_subset_1(k4_tarski(D_371,E_372),B_374)
      | v1_xboole_0(B_374)
      | ~ m1_subset_1(k4_tarski(C_370,D_371),B_374) ) ),
    inference(resolution,[status(thm)],[c_36,c_923])).

tff(c_2025,plain,(
    ! [C_383,B_384,D_385] :
      ( r2_hidden(k4_tarski(C_383,'#skF_7'),B_384)
      | ~ r2_hidden(D_385,u1_struct_0('#skF_4'))
      | ~ r2_hidden(C_383,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_384,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_384)
      | ~ m1_subset_1(k4_tarski(D_385,'#skF_7'),B_384)
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(k4_tarski(C_383,D_385),B_384) ) ),
    inference(resolution,[status(thm)],[c_1881,c_1920])).

tff(c_2034,plain,(
    ! [C_383,B_384,B_19] :
      ( r2_hidden(k4_tarski(C_383,'#skF_7'),B_384)
      | ~ r2_hidden(C_383,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_384,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_384)
      | ~ m1_subset_1(k4_tarski('#skF_2'(u1_orders_2('#skF_4'),B_19),'#skF_7'),B_384)
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(k4_tarski(C_383,'#skF_2'(u1_orders_2('#skF_4'),B_19)),B_384)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | r8_relat_2(u1_orders_2('#skF_4'),B_19)
      | ~ v1_relat_1(u1_orders_2('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_817,c_2025])).

tff(c_2064,plain,(
    ! [C_383,B_384,B_19] :
      ( r2_hidden(k4_tarski(C_383,'#skF_7'),B_384)
      | ~ r2_hidden(C_383,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_384,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_384)
      | ~ m1_subset_1(k4_tarski('#skF_2'(u1_orders_2('#skF_4'),B_19),'#skF_7'),B_384)
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(k4_tarski(C_383,'#skF_2'(u1_orders_2('#skF_4'),B_19)),B_384)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
      | r8_relat_2(u1_orders_2('#skF_4'),B_19)
      | ~ v1_relat_1(u1_orders_2('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2034])).

tff(c_2065,plain,(
    ! [C_383,B_384,B_19] :
      ( r2_hidden(k4_tarski(C_383,'#skF_7'),B_384)
      | ~ r2_hidden(C_383,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_384,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_384)
      | ~ m1_subset_1(k4_tarski('#skF_2'(u1_orders_2('#skF_4'),B_19),'#skF_7'),B_384)
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(k4_tarski(C_383,'#skF_2'(u1_orders_2('#skF_4'),B_19)),B_384)
      | r8_relat_2(u1_orders_2('#skF_4'),B_19)
      | ~ v1_relat_1(u1_orders_2('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1827,c_2064])).

tff(c_2843,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2065])).

tff(c_2846,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_2843])).

tff(c_2850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2846])).

tff(c_2852,plain,(
    v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2065])).

tff(c_6,plain,(
    ! [A_4] :
      ( r8_relat_2(u1_orders_2(A_4),u1_struct_0(A_4))
      | ~ v4_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1631,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1623])).

tff(c_1639,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_1631])).

tff(c_1828,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1639])).

tff(c_1834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1827,c_1828])).

tff(c_1835,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_1847,plain,(
    ! [C_356,B_355,A_354,C_352,B_353] :
      ( r2_hidden(k4_tarski(C_356,C_352),u1_orders_2(A_354))
      | ~ r2_hidden(k4_tarski(C_356,B_353),u1_orders_2(A_354))
      | ~ r2_hidden(C_352,B_355)
      | ~ r2_hidden(B_353,B_355)
      | ~ r2_hidden(C_356,B_355)
      | ~ r8_relat_2(u1_orders_2(A_354),B_355)
      | ~ v1_relat_1(u1_orders_2(A_354))
      | ~ r1_orders_2(A_354,B_353,C_352)
      | ~ m1_subset_1(C_352,u1_struct_0(A_354))
      | ~ m1_subset_1(B_353,u1_struct_0(A_354))
      | ~ l1_orders_2(A_354) ) ),
    inference(resolution,[status(thm)],[c_24,c_462])).

tff(c_4287,plain,(
    ! [C_562,B_565,A_566,B_564,C_563] :
      ( r2_hidden(k4_tarski(B_564,C_562),u1_orders_2(A_566))
      | ~ r2_hidden(C_562,B_565)
      | ~ r2_hidden(C_563,B_565)
      | ~ r2_hidden(B_564,B_565)
      | ~ r8_relat_2(u1_orders_2(A_566),B_565)
      | ~ v1_relat_1(u1_orders_2(A_566))
      | ~ r1_orders_2(A_566,C_563,C_562)
      | ~ m1_subset_1(C_562,u1_struct_0(A_566))
      | ~ r1_orders_2(A_566,B_564,C_563)
      | ~ m1_subset_1(C_563,u1_struct_0(A_566))
      | ~ m1_subset_1(B_564,u1_struct_0(A_566))
      | ~ l1_orders_2(A_566) ) ),
    inference(resolution,[status(thm)],[c_24,c_1847])).

tff(c_22261,plain,(
    ! [B_1319,A_1320,C_1321] :
      ( r2_hidden(k4_tarski(B_1319,'#skF_7'),u1_orders_2(A_1320))
      | ~ r2_hidden(C_1321,u1_struct_0('#skF_4'))
      | ~ r2_hidden(B_1319,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_1320),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_1320))
      | ~ r1_orders_2(A_1320,C_1321,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_1320))
      | ~ r1_orders_2(A_1320,B_1319,C_1321)
      | ~ m1_subset_1(C_1321,u1_struct_0(A_1320))
      | ~ m1_subset_1(B_1319,u1_struct_0(A_1320))
      | ~ l1_orders_2(A_1320) ) ),
    inference(resolution,[status(thm)],[c_1881,c_4287])).

tff(c_23827,plain,(
    ! [B_1394,A_1395] :
      ( r2_hidden(k4_tarski(B_1394,'#skF_7'),u1_orders_2(A_1395))
      | ~ r2_hidden(B_1394,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_1395),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_1395))
      | ~ r1_orders_2(A_1395,'#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_1395))
      | ~ r1_orders_2(A_1395,B_1394,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_1395))
      | ~ m1_subset_1(B_1394,u1_struct_0(A_1395))
      | ~ l1_orders_2(A_1395) ) ),
    inference(resolution,[status(thm)],[c_1835,c_22261])).

tff(c_23830,plain,(
    ! [B_1394] :
      ( r2_hidden(k4_tarski(B_1394,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_1394,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1394,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_1394,u1_struct_0('#skF_4'))
      | ~ v4_orders_2('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_23827])).

tff(c_23834,plain,(
    ! [B_1396] :
      ( r2_hidden(k4_tarski(B_1396,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_1396,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1396,'#skF_6')
      | ~ m1_subset_1(B_1396,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_50,c_48,c_44,c_2852,c_23830])).

tff(c_22,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_orders_2(A_29,B_33,C_35)
      | ~ r2_hidden(k4_tarski(B_33,C_35),u1_orders_2(A_29))
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_23891,plain,(
    ! [B_1396] :
      ( r1_orders_2('#skF_4',B_1396,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden(B_1396,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1396,'#skF_6')
      | ~ m1_subset_1(B_1396,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_23834,c_22])).

tff(c_23949,plain,(
    ! [B_1397] :
      ( r1_orders_2('#skF_4',B_1397,'#skF_7')
      | ~ r2_hidden(B_1397,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1397,'#skF_6')
      | ~ m1_subset_1(B_1397,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_23891])).

tff(c_24054,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_7')
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1826,c_23949])).

tff(c_24135,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_24054])).

tff(c_24137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_24135])).

%------------------------------------------------------------------------------
