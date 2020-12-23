%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:35 EST 2020

% Result     : Theorem 12.90s
% Output     : CNFRefutation 12.98s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 298 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :    8
%              Number of atoms          :  226 ( 864 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_14,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_57,plain,(
    ! [B_122,A_123] :
      ( v1_relat_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_20621,plain,(
    ! [A_1573,B_1574,C_1575,D_1576] :
      ( k7_relset_1(A_1573,B_1574,C_1575,D_1576) = k9_relat_1(C_1575,D_1576)
      | ~ m1_subset_1(C_1575,k1_zfmisc_1(k2_zfmisc_1(A_1573,B_1574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20624,plain,(
    ! [D_1576] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_1576) = k9_relat_1('#skF_5',D_1576) ),
    inference(resolution,[status(thm)],[c_32,c_20621])).

tff(c_10942,plain,(
    ! [A_949,B_950,C_951,D_952] :
      ( k7_relset_1(A_949,B_950,C_951,D_952) = k9_relat_1(C_951,D_952)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(k2_zfmisc_1(A_949,B_950))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10945,plain,(
    ! [D_952] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_952) = k9_relat_1('#skF_5',D_952) ),
    inference(resolution,[status(thm)],[c_32,c_10942])).

tff(c_1139,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k7_relset_1(A_301,B_302,C_303,D_304) = k9_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1142,plain,(
    ! [D_304] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_304) = k9_relat_1('#skF_5',D_304) ),
    inference(resolution,[status(thm)],[c_32,c_1139])).

tff(c_54,plain,
    ( r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_70,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_418,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k7_relset_1(A_195,B_196,C_197,D_198) = k9_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_425,plain,(
    ! [D_198] : k7_relset_1('#skF_4','#skF_2','#skF_5',D_198) = k9_relat_1('#skF_5',D_198) ),
    inference(resolution,[status(thm)],[c_32,c_418])).

tff(c_40,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | ~ r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_373,plain,(
    ~ r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_426,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_373])).

tff(c_100,plain,(
    ! [A_140,C_141,B_142] :
      ( r2_hidden(A_140,k1_relat_1(C_141))
      | ~ r2_hidden(k4_tarski(A_140,B_142),C_141)
      | ~ v1_relat_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_100])).

tff(c_106,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_103])).

tff(c_733,plain,(
    ! [A_241,C_242,B_243,D_244] :
      ( r2_hidden(A_241,k9_relat_1(C_242,B_243))
      | ~ r2_hidden(D_244,B_243)
      | ~ r2_hidden(k4_tarski(D_244,A_241),C_242)
      | ~ r2_hidden(D_244,k1_relat_1(C_242))
      | ~ v1_relat_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_827,plain,(
    ! [A_255,C_256] :
      ( r2_hidden(A_255,k9_relat_1(C_256,'#skF_3'))
      | ~ r2_hidden(k4_tarski('#skF_7',A_255),C_256)
      | ~ r2_hidden('#skF_7',k1_relat_1(C_256))
      | ~ v1_relat_1(C_256) ) ),
    inference(resolution,[status(thm)],[c_64,c_733])).

tff(c_889,plain,
    ( r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_827])).

tff(c_909,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_106,c_889])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_909])).

tff(c_967,plain,(
    ! [F_263] :
      ( ~ r2_hidden(F_263,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_263,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_263,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_974,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_967])).

tff(c_981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_974])).

tff(c_982,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1146,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_982])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_16,B_17,C_18),B_17)
      | ~ r2_hidden(A_16,k9_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1247,plain,(
    ! [A_327,B_328,C_329] :
      ( r2_hidden(k4_tarski('#skF_1'(A_327,B_328,C_329),A_327),C_329)
      | ~ r2_hidden(A_327,k9_relat_1(C_329,B_328))
      | ~ v1_relat_1(C_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_983,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1082,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_983,c_48])).

tff(c_1254,plain,(
    ! [B_328] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_328,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_328,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_328))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1247,c_1082])).

tff(c_2326,plain,(
    ! [B_458] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_458,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_458,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_458)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1254])).

tff(c_2334,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_2326])).

tff(c_2340,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1146,c_2334])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2807,plain,(
    ! [A_509,B_510,C_511,A_512] :
      ( r2_hidden(k4_tarski('#skF_1'(A_509,B_510,C_511),A_509),A_512)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(A_512))
      | ~ r2_hidden(A_509,k9_relat_1(C_511,B_510))
      | ~ v1_relat_1(C_511) ) ),
    inference(resolution,[status(thm)],[c_1247,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10538,plain,(
    ! [C_866,D_865,C_864,B_867,A_863] :
      ( r2_hidden('#skF_1'(A_863,B_867,C_864),C_866)
      | ~ m1_subset_1(C_864,k1_zfmisc_1(k2_zfmisc_1(C_866,D_865)))
      | ~ r2_hidden(A_863,k9_relat_1(C_864,B_867))
      | ~ v1_relat_1(C_864) ) ),
    inference(resolution,[status(thm)],[c_2807,c_6])).

tff(c_10546,plain,(
    ! [A_863,B_867] :
      ( r2_hidden('#skF_1'(A_863,B_867,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_863,k9_relat_1('#skF_5',B_867))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_10538])).

tff(c_10552,plain,(
    ! [A_868,B_869] :
      ( r2_hidden('#skF_1'(A_868,B_869,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_868,k9_relat_1('#skF_5',B_869)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10546])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10620,plain,(
    ! [A_870,B_871] :
      ( m1_subset_1('#skF_1'(A_870,B_871,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_870,k9_relat_1('#skF_5',B_871)) ) ),
    inference(resolution,[status(thm)],[c_10552,c_10])).

tff(c_10647,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1146,c_10620])).

tff(c_10663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2340,c_10647])).

tff(c_10664,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10999,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10945,c_10664])).

tff(c_10946,plain,(
    ! [A_953,B_954,C_955] :
      ( r2_hidden(k4_tarski('#skF_1'(A_953,B_954,C_955),A_953),C_955)
      | ~ r2_hidden(A_953,k9_relat_1(C_955,B_954))
      | ~ v1_relat_1(C_955) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10665,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10825,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10665,c_52])).

tff(c_10955,plain,(
    ! [B_954] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_954,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_954,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_954))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10946,c_10825])).

tff(c_11979,plain,(
    ! [B_1077] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1077,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1077,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_1077)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10955])).

tff(c_11987,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_11979])).

tff(c_11993,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10999,c_11987])).

tff(c_12370,plain,(
    ! [A_1136,B_1137,C_1138,A_1139] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1136,B_1137,C_1138),A_1136),A_1139)
      | ~ m1_subset_1(C_1138,k1_zfmisc_1(A_1139))
      | ~ r2_hidden(A_1136,k9_relat_1(C_1138,B_1137))
      | ~ v1_relat_1(C_1138) ) ),
    inference(resolution,[status(thm)],[c_10946,c_8])).

tff(c_20346,plain,(
    ! [C_1516,B_1512,C_1514,A_1515,D_1513] :
      ( r2_hidden('#skF_1'(A_1515,B_1512,C_1516),C_1514)
      | ~ m1_subset_1(C_1516,k1_zfmisc_1(k2_zfmisc_1(C_1514,D_1513)))
      | ~ r2_hidden(A_1515,k9_relat_1(C_1516,B_1512))
      | ~ v1_relat_1(C_1516) ) ),
    inference(resolution,[status(thm)],[c_12370,c_6])).

tff(c_20357,plain,(
    ! [A_1515,B_1512] :
      ( r2_hidden('#skF_1'(A_1515,B_1512,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1515,k9_relat_1('#skF_5',B_1512))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_20346])).

tff(c_20364,plain,(
    ! [A_1517,B_1518] :
      ( r2_hidden('#skF_1'(A_1517,B_1518,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1517,k9_relat_1('#skF_5',B_1518)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_20357])).

tff(c_20432,plain,(
    ! [A_1519,B_1520] :
      ( m1_subset_1('#skF_1'(A_1519,B_1520,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1519,k9_relat_1('#skF_5',B_1520)) ) ),
    inference(resolution,[status(thm)],[c_20364,c_10])).

tff(c_20455,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10999,c_20432])).

tff(c_20474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11993,c_20455])).

tff(c_20475,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_20631,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20624,c_20475])).

tff(c_20641,plain,(
    ! [A_1578,B_1579,C_1580] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1578,B_1579,C_1580),A_1578),C_1580)
      | ~ r2_hidden(A_1578,k9_relat_1(C_1580,B_1579))
      | ~ v1_relat_1(C_1580) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20476,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20549,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski(F_117,'#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20476,c_44])).

tff(c_20648,plain,(
    ! [B_1579] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1579,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1579,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_1579))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20641,c_20549])).

tff(c_20883,plain,(
    ! [B_1610] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1610,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1610,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5',B_1610)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_20648])).

tff(c_20887,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_20883])).

tff(c_20890,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_20631,c_20887])).

tff(c_21666,plain,(
    ! [A_1723,B_1724,C_1725,A_1726] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1723,B_1724,C_1725),A_1723),A_1726)
      | ~ m1_subset_1(C_1725,k1_zfmisc_1(A_1726))
      | ~ r2_hidden(A_1723,k9_relat_1(C_1725,B_1724))
      | ~ v1_relat_1(C_1725) ) ),
    inference(resolution,[status(thm)],[c_20641,c_8])).

tff(c_29744,plain,(
    ! [C_2113,A_2117,D_2115,B_2114,C_2116] :
      ( r2_hidden('#skF_1'(A_2117,B_2114,C_2113),C_2116)
      | ~ m1_subset_1(C_2113,k1_zfmisc_1(k2_zfmisc_1(C_2116,D_2115)))
      | ~ r2_hidden(A_2117,k9_relat_1(C_2113,B_2114))
      | ~ v1_relat_1(C_2113) ) ),
    inference(resolution,[status(thm)],[c_21666,c_6])).

tff(c_29752,plain,(
    ! [A_2117,B_2114] :
      ( r2_hidden('#skF_1'(A_2117,B_2114,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_2117,k9_relat_1('#skF_5',B_2114))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_29744])).

tff(c_29758,plain,(
    ! [A_2118,B_2119] :
      ( r2_hidden('#skF_1'(A_2118,B_2119,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_2118,k9_relat_1('#skF_5',B_2119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_29752])).

tff(c_29835,plain,(
    ! [A_2120,B_2121] :
      ( m1_subset_1('#skF_1'(A_2120,B_2121,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_2120,k9_relat_1('#skF_5',B_2121)) ) ),
    inference(resolution,[status(thm)],[c_29758,c_10])).

tff(c_29858,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20631,c_29835])).

tff(c_29877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20890,c_29858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.90/6.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.93/6.33  
% 12.93/6.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.93/6.33  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 12.93/6.33  
% 12.93/6.33  %Foreground sorts:
% 12.93/6.33  
% 12.93/6.33  
% 12.93/6.33  %Background operators:
% 12.93/6.33  
% 12.93/6.33  
% 12.93/6.33  %Foreground operators:
% 12.93/6.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.93/6.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.93/6.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.93/6.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.93/6.33  tff('#skF_7', type, '#skF_7': $i).
% 12.93/6.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.93/6.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.93/6.33  tff('#skF_5', type, '#skF_5': $i).
% 12.93/6.33  tff('#skF_6', type, '#skF_6': $i).
% 12.93/6.33  tff('#skF_2', type, '#skF_2': $i).
% 12.93/6.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.93/6.33  tff('#skF_3', type, '#skF_3': $i).
% 12.93/6.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.93/6.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.93/6.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.93/6.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.93/6.33  tff('#skF_4', type, '#skF_4': $i).
% 12.93/6.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.93/6.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.93/6.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.93/6.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.93/6.33  
% 12.98/6.35  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.98/6.35  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 12.98/6.35  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.98/6.35  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.98/6.35  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 12.98/6.35  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 12.98/6.35  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 12.98/6.35  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 12.98/6.35  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 12.98/6.35  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.98/6.35  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_57, plain, (![B_122, A_123]: (v1_relat_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.98/6.35  tff(c_60, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_57])).
% 12.98/6.35  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_60])).
% 12.98/6.35  tff(c_20621, plain, (![A_1573, B_1574, C_1575, D_1576]: (k7_relset_1(A_1573, B_1574, C_1575, D_1576)=k9_relat_1(C_1575, D_1576) | ~m1_subset_1(C_1575, k1_zfmisc_1(k2_zfmisc_1(A_1573, B_1574))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.98/6.35  tff(c_20624, plain, (![D_1576]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_1576)=k9_relat_1('#skF_5', D_1576))), inference(resolution, [status(thm)], [c_32, c_20621])).
% 12.98/6.35  tff(c_10942, plain, (![A_949, B_950, C_951, D_952]: (k7_relset_1(A_949, B_950, C_951, D_952)=k9_relat_1(C_951, D_952) | ~m1_subset_1(C_951, k1_zfmisc_1(k2_zfmisc_1(A_949, B_950))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.98/6.35  tff(c_10945, plain, (![D_952]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_952)=k9_relat_1('#skF_5', D_952))), inference(resolution, [status(thm)], [c_32, c_10942])).
% 12.98/6.35  tff(c_1139, plain, (![A_301, B_302, C_303, D_304]: (k7_relset_1(A_301, B_302, C_303, D_304)=k9_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.98/6.35  tff(c_1142, plain, (![D_304]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_304)=k9_relat_1('#skF_5', D_304))), inference(resolution, [status(thm)], [c_32, c_1139])).
% 12.98/6.35  tff(c_54, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_70, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 12.98/6.35  tff(c_46, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_64, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 12.98/6.35  tff(c_50, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 12.98/6.35  tff(c_418, plain, (![A_195, B_196, C_197, D_198]: (k7_relset_1(A_195, B_196, C_197, D_198)=k9_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.98/6.35  tff(c_425, plain, (![D_198]: (k7_relset_1('#skF_4', '#skF_2', '#skF_5', D_198)=k9_relat_1('#skF_5', D_198))), inference(resolution, [status(thm)], [c_32, c_418])).
% 12.98/6.35  tff(c_40, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | ~r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_373, plain, (~r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 12.98/6.35  tff(c_426, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_373])).
% 12.98/6.35  tff(c_100, plain, (![A_140, C_141, B_142]: (r2_hidden(A_140, k1_relat_1(C_141)) | ~r2_hidden(k4_tarski(A_140, B_142), C_141) | ~v1_relat_1(C_141))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.98/6.35  tff(c_103, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_100])).
% 12.98/6.35  tff(c_106, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_103])).
% 12.98/6.35  tff(c_733, plain, (![A_241, C_242, B_243, D_244]: (r2_hidden(A_241, k9_relat_1(C_242, B_243)) | ~r2_hidden(D_244, B_243) | ~r2_hidden(k4_tarski(D_244, A_241), C_242) | ~r2_hidden(D_244, k1_relat_1(C_242)) | ~v1_relat_1(C_242))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.98/6.35  tff(c_827, plain, (![A_255, C_256]: (r2_hidden(A_255, k9_relat_1(C_256, '#skF_3')) | ~r2_hidden(k4_tarski('#skF_7', A_255), C_256) | ~r2_hidden('#skF_7', k1_relat_1(C_256)) | ~v1_relat_1(C_256))), inference(resolution, [status(thm)], [c_64, c_733])).
% 12.98/6.35  tff(c_889, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_827])).
% 12.98/6.35  tff(c_909, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_106, c_889])).
% 12.98/6.35  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_909])).
% 12.98/6.35  tff(c_967, plain, (![F_263]: (~r2_hidden(F_263, '#skF_3') | ~r2_hidden(k4_tarski(F_263, '#skF_6'), '#skF_5') | ~m1_subset_1(F_263, '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 12.98/6.35  tff(c_974, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_967])).
% 12.98/6.35  tff(c_981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_974])).
% 12.98/6.35  tff(c_982, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 12.98/6.35  tff(c_1146, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_982])).
% 12.98/6.35  tff(c_18, plain, (![A_16, B_17, C_18]: (r2_hidden('#skF_1'(A_16, B_17, C_18), B_17) | ~r2_hidden(A_16, k9_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.98/6.35  tff(c_1247, plain, (![A_327, B_328, C_329]: (r2_hidden(k4_tarski('#skF_1'(A_327, B_328, C_329), A_327), C_329) | ~r2_hidden(A_327, k9_relat_1(C_329, B_328)) | ~v1_relat_1(C_329))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.98/6.35  tff(c_983, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 12.98/6.35  tff(c_48, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_1082, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_983, c_48])).
% 12.98/6.35  tff(c_1254, plain, (![B_328]: (~r2_hidden('#skF_1'('#skF_6', B_328, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_328, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_328)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1247, c_1082])).
% 12.98/6.35  tff(c_2326, plain, (![B_458]: (~r2_hidden('#skF_1'('#skF_6', B_458, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_458, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_458)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1254])).
% 12.98/6.35  tff(c_2334, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_2326])).
% 12.98/6.35  tff(c_2340, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1146, c_2334])).
% 12.98/6.35  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.98/6.35  tff(c_2807, plain, (![A_509, B_510, C_511, A_512]: (r2_hidden(k4_tarski('#skF_1'(A_509, B_510, C_511), A_509), A_512) | ~m1_subset_1(C_511, k1_zfmisc_1(A_512)) | ~r2_hidden(A_509, k9_relat_1(C_511, B_510)) | ~v1_relat_1(C_511))), inference(resolution, [status(thm)], [c_1247, c_8])).
% 12.98/6.35  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.98/6.35  tff(c_10538, plain, (![C_866, D_865, C_864, B_867, A_863]: (r2_hidden('#skF_1'(A_863, B_867, C_864), C_866) | ~m1_subset_1(C_864, k1_zfmisc_1(k2_zfmisc_1(C_866, D_865))) | ~r2_hidden(A_863, k9_relat_1(C_864, B_867)) | ~v1_relat_1(C_864))), inference(resolution, [status(thm)], [c_2807, c_6])).
% 12.98/6.35  tff(c_10546, plain, (![A_863, B_867]: (r2_hidden('#skF_1'(A_863, B_867, '#skF_5'), '#skF_4') | ~r2_hidden(A_863, k9_relat_1('#skF_5', B_867)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_10538])).
% 12.98/6.35  tff(c_10552, plain, (![A_868, B_869]: (r2_hidden('#skF_1'(A_868, B_869, '#skF_5'), '#skF_4') | ~r2_hidden(A_868, k9_relat_1('#skF_5', B_869)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10546])).
% 12.98/6.35  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.98/6.35  tff(c_10620, plain, (![A_870, B_871]: (m1_subset_1('#skF_1'(A_870, B_871, '#skF_5'), '#skF_4') | ~r2_hidden(A_870, k9_relat_1('#skF_5', B_871)))), inference(resolution, [status(thm)], [c_10552, c_10])).
% 12.98/6.35  tff(c_10647, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1146, c_10620])).
% 12.98/6.35  tff(c_10663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2340, c_10647])).
% 12.98/6.35  tff(c_10664, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 12.98/6.35  tff(c_10999, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10945, c_10664])).
% 12.98/6.35  tff(c_10946, plain, (![A_953, B_954, C_955]: (r2_hidden(k4_tarski('#skF_1'(A_953, B_954, C_955), A_953), C_955) | ~r2_hidden(A_953, k9_relat_1(C_955, B_954)) | ~v1_relat_1(C_955))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.98/6.35  tff(c_10665, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 12.98/6.35  tff(c_52, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_10825, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_10665, c_52])).
% 12.98/6.35  tff(c_10955, plain, (![B_954]: (~r2_hidden('#skF_1'('#skF_6', B_954, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_954, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_954)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10946, c_10825])).
% 12.98/6.35  tff(c_11979, plain, (![B_1077]: (~r2_hidden('#skF_1'('#skF_6', B_1077, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_1077, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_1077)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10955])).
% 12.98/6.35  tff(c_11987, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_11979])).
% 12.98/6.35  tff(c_11993, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10999, c_11987])).
% 12.98/6.35  tff(c_12370, plain, (![A_1136, B_1137, C_1138, A_1139]: (r2_hidden(k4_tarski('#skF_1'(A_1136, B_1137, C_1138), A_1136), A_1139) | ~m1_subset_1(C_1138, k1_zfmisc_1(A_1139)) | ~r2_hidden(A_1136, k9_relat_1(C_1138, B_1137)) | ~v1_relat_1(C_1138))), inference(resolution, [status(thm)], [c_10946, c_8])).
% 12.98/6.35  tff(c_20346, plain, (![C_1516, B_1512, C_1514, A_1515, D_1513]: (r2_hidden('#skF_1'(A_1515, B_1512, C_1516), C_1514) | ~m1_subset_1(C_1516, k1_zfmisc_1(k2_zfmisc_1(C_1514, D_1513))) | ~r2_hidden(A_1515, k9_relat_1(C_1516, B_1512)) | ~v1_relat_1(C_1516))), inference(resolution, [status(thm)], [c_12370, c_6])).
% 12.98/6.35  tff(c_20357, plain, (![A_1515, B_1512]: (r2_hidden('#skF_1'(A_1515, B_1512, '#skF_5'), '#skF_4') | ~r2_hidden(A_1515, k9_relat_1('#skF_5', B_1512)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_20346])).
% 12.98/6.35  tff(c_20364, plain, (![A_1517, B_1518]: (r2_hidden('#skF_1'(A_1517, B_1518, '#skF_5'), '#skF_4') | ~r2_hidden(A_1517, k9_relat_1('#skF_5', B_1518)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_20357])).
% 12.98/6.35  tff(c_20432, plain, (![A_1519, B_1520]: (m1_subset_1('#skF_1'(A_1519, B_1520, '#skF_5'), '#skF_4') | ~r2_hidden(A_1519, k9_relat_1('#skF_5', B_1520)))), inference(resolution, [status(thm)], [c_20364, c_10])).
% 12.98/6.35  tff(c_20455, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10999, c_20432])).
% 12.98/6.35  tff(c_20474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11993, c_20455])).
% 12.98/6.35  tff(c_20475, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 12.98/6.35  tff(c_20631, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20624, c_20475])).
% 12.98/6.35  tff(c_20641, plain, (![A_1578, B_1579, C_1580]: (r2_hidden(k4_tarski('#skF_1'(A_1578, B_1579, C_1580), A_1578), C_1580) | ~r2_hidden(A_1578, k9_relat_1(C_1580, B_1579)) | ~v1_relat_1(C_1580))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.98/6.35  tff(c_20476, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 12.98/6.35  tff(c_44, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.98/6.35  tff(c_20549, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski(F_117, '#skF_6'), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_20476, c_44])).
% 12.98/6.35  tff(c_20648, plain, (![B_1579]: (~r2_hidden('#skF_1'('#skF_6', B_1579, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_1579, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_1579)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_20641, c_20549])).
% 12.98/6.35  tff(c_20883, plain, (![B_1610]: (~r2_hidden('#skF_1'('#skF_6', B_1610, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_1610, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', B_1610)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_20648])).
% 12.98/6.35  tff(c_20887, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_20883])).
% 12.98/6.35  tff(c_20890, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_20631, c_20887])).
% 12.98/6.35  tff(c_21666, plain, (![A_1723, B_1724, C_1725, A_1726]: (r2_hidden(k4_tarski('#skF_1'(A_1723, B_1724, C_1725), A_1723), A_1726) | ~m1_subset_1(C_1725, k1_zfmisc_1(A_1726)) | ~r2_hidden(A_1723, k9_relat_1(C_1725, B_1724)) | ~v1_relat_1(C_1725))), inference(resolution, [status(thm)], [c_20641, c_8])).
% 12.98/6.35  tff(c_29744, plain, (![C_2113, A_2117, D_2115, B_2114, C_2116]: (r2_hidden('#skF_1'(A_2117, B_2114, C_2113), C_2116) | ~m1_subset_1(C_2113, k1_zfmisc_1(k2_zfmisc_1(C_2116, D_2115))) | ~r2_hidden(A_2117, k9_relat_1(C_2113, B_2114)) | ~v1_relat_1(C_2113))), inference(resolution, [status(thm)], [c_21666, c_6])).
% 12.98/6.35  tff(c_29752, plain, (![A_2117, B_2114]: (r2_hidden('#skF_1'(A_2117, B_2114, '#skF_5'), '#skF_4') | ~r2_hidden(A_2117, k9_relat_1('#skF_5', B_2114)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_29744])).
% 12.98/6.35  tff(c_29758, plain, (![A_2118, B_2119]: (r2_hidden('#skF_1'(A_2118, B_2119, '#skF_5'), '#skF_4') | ~r2_hidden(A_2118, k9_relat_1('#skF_5', B_2119)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_29752])).
% 12.98/6.35  tff(c_29835, plain, (![A_2120, B_2121]: (m1_subset_1('#skF_1'(A_2120, B_2121, '#skF_5'), '#skF_4') | ~r2_hidden(A_2120, k9_relat_1('#skF_5', B_2121)))), inference(resolution, [status(thm)], [c_29758, c_10])).
% 12.98/6.35  tff(c_29858, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_20631, c_29835])).
% 12.98/6.35  tff(c_29877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20890, c_29858])).
% 12.98/6.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/6.35  
% 12.98/6.35  Inference rules
% 12.98/6.35  ----------------------
% 12.98/6.35  #Ref     : 0
% 12.98/6.35  #Sup     : 8307
% 12.98/6.35  #Fact    : 0
% 12.98/6.35  #Define  : 0
% 12.98/6.35  #Split   : 13
% 12.98/6.35  #Chain   : 0
% 12.98/6.35  #Close   : 0
% 12.98/6.35  
% 12.98/6.35  Ordering : KBO
% 12.98/6.35  
% 12.98/6.35  Simplification rules
% 12.98/6.35  ----------------------
% 12.98/6.35  #Subsume      : 69
% 12.98/6.35  #Demod        : 173
% 12.98/6.35  #Tautology    : 38
% 12.98/6.35  #SimpNegUnit  : 9
% 12.98/6.35  #BackRed      : 19
% 12.98/6.35  
% 12.98/6.35  #Partial instantiations: 0
% 12.98/6.35  #Strategies tried      : 1
% 12.98/6.35  
% 12.98/6.35  Timing (in seconds)
% 12.98/6.35  ----------------------
% 12.98/6.36  Preprocessing        : 0.33
% 12.98/6.36  Parsing              : 0.17
% 12.98/6.36  CNF conversion       : 0.03
% 12.98/6.36  Main loop            : 5.24
% 12.98/6.36  Inferencing          : 1.21
% 12.98/6.36  Reduction            : 1.27
% 12.98/6.36  Demodulation         : 0.85
% 12.98/6.36  BG Simplification    : 0.16
% 12.98/6.36  Subsumption          : 2.11
% 12.98/6.36  Abstraction          : 0.20
% 12.98/6.36  MUC search           : 0.00
% 12.98/6.36  Cooper               : 0.00
% 12.98/6.36  Total                : 5.62
% 12.98/6.36  Index Insertion      : 0.00
% 12.98/6.36  Index Deletion       : 0.00
% 12.98/6.36  Index Matching       : 0.00
% 12.98/6.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
