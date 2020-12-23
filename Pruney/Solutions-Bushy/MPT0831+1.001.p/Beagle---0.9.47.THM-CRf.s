%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0831+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:54 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 248 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 ( 588 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2044,plain,(
    ! [A_417,B_418,D_419] :
      ( r2_relset_1(A_417,B_418,D_419,D_419)
      | ~ m1_subset_1(D_419,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2051,plain,(
    r2_relset_1('#skF_6','#skF_5','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_2044])).

tff(c_60,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_69,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_2379,plain,(
    ! [A_537,B_538,C_539] :
      ( r2_hidden(k4_tarski('#skF_1'(A_537,B_538,C_539),'#skF_2'(A_537,B_538,C_539)),A_537)
      | r2_hidden(k4_tarski('#skF_3'(A_537,B_538,C_539),'#skF_4'(A_537,B_538,C_539)),C_539)
      | k7_relat_1(A_537,B_538) = C_539
      | ~ v1_relat_1(C_539)
      | ~ v1_relat_1(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_4,B_15,C_16] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_4,B_15,C_16),'#skF_2'(A_4,B_15,C_16)),C_16)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_15,C_16),'#skF_4'(A_4,B_15,C_16)),C_16)
      | k7_relat_1(A_4,B_15) = C_16
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2462,plain,(
    ! [A_540,B_541] :
      ( r2_hidden(k4_tarski('#skF_3'(A_540,B_541,A_540),'#skF_4'(A_540,B_541,A_540)),A_540)
      | k7_relat_1(A_540,B_541) = A_540
      | ~ v1_relat_1(A_540) ) ),
    inference(resolution,[status(thm)],[c_2379,c_10])).

tff(c_110,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_relset_1(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_117,plain,(
    r2_relset_1('#skF_6','#skF_5','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    ! [B_60,A_61,A_62] :
      ( ~ v1_xboole_0(B_60)
      | ~ r2_hidden(A_61,A_62)
      | ~ r1_tarski(A_62,B_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_123,plain,(
    ! [B_84,B_85,A_86] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(B_85,B_84)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_129,plain,(
    ! [A_86] :
      ( ~ v1_xboole_0('#skF_7')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_86,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_130,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_12,plain,(
    ! [A_4,B_15,C_16] :
      ( r2_hidden(k4_tarski('#skF_1'(A_4,B_15,C_16),'#skF_2'(A_4,B_15,C_16)),A_4)
      | r2_hidden(k4_tarski('#skF_3'(A_4,B_15,C_16),'#skF_4'(A_4,B_15,C_16)),C_16)
      | k7_relat_1(A_4,B_15) = C_16
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_498,plain,(
    ! [A_191,B_192,C_193] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_191,B_192,C_193),'#skF_2'(A_191,B_192,C_193)),C_193)
      | r2_hidden(k4_tarski('#skF_3'(A_191,B_192,C_193),'#skF_4'(A_191,B_192,C_193)),C_193)
      | k7_relat_1(A_191,B_192) = C_193
      | ~ v1_relat_1(C_193)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_519,plain,(
    ! [A_194,B_195] :
      ( r2_hidden(k4_tarski('#skF_3'(A_194,B_195,A_194),'#skF_4'(A_194,B_195,A_194)),A_194)
      | k7_relat_1(A_194,B_195) = A_194
      | ~ v1_relat_1(A_194) ) ),
    inference(resolution,[status(thm)],[c_12,c_498])).

tff(c_82,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_59,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_83,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_98,plain,(
    ! [A_71,C_72,B_73] :
      ( m1_subset_1(A_71,C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_104,plain,(
    ! [A_71] :
      ( m1_subset_1(A_71,k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(A_71,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_93,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r2_hidden(A_67,C_68)
      | ~ r2_hidden(k4_tarski(A_67,B_69),k2_zfmisc_1(C_68,D_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_203,plain,(
    ! [A_122,C_123,D_124,B_125] :
      ( r2_hidden(A_122,C_123)
      | v1_xboole_0(k2_zfmisc_1(C_123,D_124))
      | ~ m1_subset_1(k4_tarski(A_122,B_125),k2_zfmisc_1(C_123,D_124)) ) ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_207,plain,(
    ! [A_122,B_125] :
      ( r2_hidden(A_122,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_122,B_125),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_104,c_203])).

tff(c_210,plain,(
    ! [A_122,B_125] :
      ( r2_hidden(A_122,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_122,B_125),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_207])).

tff(c_523,plain,(
    ! [B_195] :
      ( r2_hidden('#skF_3'('#skF_8',B_195,'#skF_8'),'#skF_6')
      | k7_relat_1('#skF_8',B_195) = '#skF_8'
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_519,c_210])).

tff(c_560,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_3'('#skF_8',B_196,'#skF_8'),'#skF_6')
      | k7_relat_1('#skF_8',B_196) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_523])).

tff(c_103,plain,(
    ! [A_71,B_38,A_37] :
      ( m1_subset_1(A_71,B_38)
      | ~ r2_hidden(A_71,A_37)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_565,plain,(
    ! [B_196,B_38] :
      ( m1_subset_1('#skF_3'('#skF_8',B_196,'#skF_8'),B_38)
      | ~ r1_tarski('#skF_6',B_38)
      | k7_relat_1('#skF_8',B_196) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_560,c_103])).

tff(c_515,plain,(
    ! [A_4,B_15] :
      ( r2_hidden(k4_tarski('#skF_3'(A_4,B_15,A_4),'#skF_4'(A_4,B_15,A_4)),A_4)
      | k7_relat_1(A_4,B_15) = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_498])).

tff(c_965,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden(k4_tarski('#skF_1'(A_237,B_238,C_239),'#skF_2'(A_237,B_238,C_239)),A_237)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_237,B_238,C_239),'#skF_4'(A_237,B_238,C_239)),A_237)
      | ~ r2_hidden('#skF_3'(A_237,B_238,C_239),B_238)
      | k7_relat_1(A_237,B_238) = C_239
      | ~ v1_relat_1(C_239)
      | ~ v1_relat_1(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_4,B_15,C_16] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_4,B_15,C_16),'#skF_2'(A_4,B_15,C_16)),C_16)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_4,B_15,C_16),'#skF_4'(A_4,B_15,C_16)),A_4)
      | ~ r2_hidden('#skF_3'(A_4,B_15,C_16),B_15)
      | k7_relat_1(A_4,B_15) = C_16
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1167,plain,(
    ! [A_250,B_251] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_250,B_251,A_250),'#skF_4'(A_250,B_251,A_250)),A_250)
      | ~ r2_hidden('#skF_3'(A_250,B_251,A_250),B_251)
      | k7_relat_1(A_250,B_251) = A_250
      | ~ v1_relat_1(A_250) ) ),
    inference(resolution,[status(thm)],[c_965,c_4])).

tff(c_1208,plain,(
    ! [A_252,B_253] :
      ( ~ r2_hidden('#skF_3'(A_252,B_253,A_252),B_253)
      | k7_relat_1(A_252,B_253) = A_252
      | ~ v1_relat_1(A_252) ) ),
    inference(resolution,[status(thm)],[c_515,c_1167])).

tff(c_1221,plain,(
    ! [A_254,B_255] :
      ( k7_relat_1(A_254,B_255) = A_254
      | ~ v1_relat_1(A_254)
      | v1_xboole_0(B_255)
      | ~ m1_subset_1('#skF_3'(A_254,B_255,A_254),B_255) ) ),
    inference(resolution,[status(thm)],[c_34,c_1208])).

tff(c_1225,plain,(
    ! [B_38] :
      ( ~ v1_relat_1('#skF_8')
      | v1_xboole_0(B_38)
      | ~ r1_tarski('#skF_6',B_38)
      | k7_relat_1('#skF_8',B_38) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_565,c_1221])).

tff(c_1241,plain,(
    ! [B_256] :
      ( v1_xboole_0(B_256)
      | ~ r1_tarski('#skF_6',B_256)
      | k7_relat_1('#skF_8',B_256) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1225])).

tff(c_1244,plain,
    ( v1_xboole_0('#skF_7')
    | k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46,c_1241])).

tff(c_1247,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1244])).

tff(c_156,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k5_relset_1(A_99,B_100,C_101,D_102) = k7_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [D_102] : k5_relset_1('#skF_6','#skF_5','#skF_8',D_102) = k7_relat_1('#skF_8',D_102) ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_6','#skF_5',k5_relset_1('#skF_6','#skF_5','#skF_8','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    ~ r2_relset_1('#skF_6','#skF_5',k7_relat_1('#skF_8','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_1248,plain,(
    ~ r2_relset_1('#skF_6','#skF_5','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_164])).

tff(c_1251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1248])).

tff(c_1253,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_1827,plain,(
    ! [A_387,B_388,C_389] :
      ( r2_hidden(k4_tarski('#skF_1'(A_387,B_388,C_389),'#skF_2'(A_387,B_388,C_389)),A_387)
      | r2_hidden(k4_tarski('#skF_3'(A_387,B_388,C_389),'#skF_4'(A_387,B_388,C_389)),C_389)
      | k7_relat_1(A_387,B_388) = C_389
      | ~ v1_relat_1(C_389)
      | ~ v1_relat_1(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1919,plain,(
    ! [A_390,B_391] :
      ( r2_hidden(k4_tarski('#skF_3'(A_390,B_391,A_390),'#skF_4'(A_390,B_391,A_390)),A_390)
      | k7_relat_1(A_390,B_391) = A_390
      | ~ v1_relat_1(A_390) ) ),
    inference(resolution,[status(thm)],[c_1827,c_10])).

tff(c_1317,plain,(
    ! [A_285,C_286,D_287,B_288] :
      ( r2_hidden(A_285,C_286)
      | v1_xboole_0(k2_zfmisc_1(C_286,D_287))
      | ~ m1_subset_1(k4_tarski(A_285,B_288),k2_zfmisc_1(C_286,D_287)) ) ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_1321,plain,(
    ! [A_285,B_288] :
      ( r2_hidden(A_285,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_285,B_288),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_104,c_1317])).

tff(c_1324,plain,(
    ! [A_285,B_288] :
      ( r2_hidden(A_285,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_285,B_288),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1321])).

tff(c_1933,plain,(
    ! [B_391] :
      ( r2_hidden('#skF_3'('#skF_8',B_391,'#skF_8'),'#skF_6')
      | k7_relat_1('#skF_8',B_391) = '#skF_8'
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1919,c_1324])).

tff(c_1968,plain,(
    ! [B_392] :
      ( r2_hidden('#skF_3'('#skF_8',B_392,'#skF_8'),'#skF_6')
      | k7_relat_1('#skF_8',B_392) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1933])).

tff(c_81,plain,(
    ! [B_38,A_59,A_37] :
      ( ~ v1_xboole_0(B_38)
      | ~ r2_hidden(A_59,A_37)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_1974,plain,(
    ! [B_38,B_392] :
      ( ~ v1_xboole_0(B_38)
      | ~ r1_tarski('#skF_6',B_38)
      | k7_relat_1('#skF_8',B_392) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1968,c_81])).

tff(c_1983,plain,(
    ! [B_394] :
      ( ~ v1_xboole_0(B_394)
      | ~ r1_tarski('#skF_6',B_394) ) ),
    inference(splitLeft,[status(thm)],[c_1974])).

tff(c_1986,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_1983])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_1986])).

tff(c_1991,plain,(
    ! [B_392] : k7_relat_1('#skF_8',B_392) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1974])).

tff(c_1280,plain,(
    ! [A_270,B_271,C_272,D_273] :
      ( k5_relset_1(A_270,B_271,C_272,D_273) = k7_relat_1(C_272,D_273)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1287,plain,(
    ! [D_273] : k5_relset_1('#skF_6','#skF_5','#skF_8',D_273) = k7_relat_1('#skF_8',D_273) ),
    inference(resolution,[status(thm)],[c_48,c_1280])).

tff(c_1288,plain,(
    ~ r2_relset_1('#skF_6','#skF_5',k7_relat_1('#skF_8','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_44])).

tff(c_1994,plain,(
    ~ r2_relset_1('#skF_6','#skF_5','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1991,c_1288])).

tff(c_1998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1994])).

tff(c_1999,plain,(
    ! [A_59] : ~ r2_hidden(A_59,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2492,plain,(
    ! [B_541] :
      ( k7_relat_1('#skF_8',B_541) = '#skF_8'
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2462,c_1999])).

tff(c_2503,plain,(
    ! [B_541] : k7_relat_1('#skF_8',B_541) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2492])).

tff(c_2081,plain,(
    ! [A_435,B_436,C_437,D_438] :
      ( k5_relset_1(A_435,B_436,C_437,D_438) = k7_relat_1(C_437,D_438)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2088,plain,(
    ! [D_438] : k5_relset_1('#skF_6','#skF_5','#skF_8',D_438) = k7_relat_1('#skF_8',D_438) ),
    inference(resolution,[status(thm)],[c_48,c_2081])).

tff(c_2089,plain,(
    ~ r2_relset_1('#skF_6','#skF_5',k7_relat_1('#skF_8','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_44])).

tff(c_2505,plain,(
    ~ r2_relset_1('#skF_6','#skF_5','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_2089])).

tff(c_2509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2505])).

%------------------------------------------------------------------------------
