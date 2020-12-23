%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:39 EST 2020

% Result     : Theorem 16.32s
% Output     : CNFRefutation 16.41s
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
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_14,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_57,plain,(
    ! [B_122,A_123] :
      ( v1_relat_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_19937,plain,(
    ! [A_1536,B_1537,C_1538,D_1539] :
      ( k8_relset_1(A_1536,B_1537,C_1538,D_1539) = k10_relat_1(C_1538,D_1539)
      | ~ m1_subset_1(C_1538,k1_zfmisc_1(k2_zfmisc_1(A_1536,B_1537))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19940,plain,(
    ! [D_1539] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_1539) = k10_relat_1('#skF_5',D_1539) ),
    inference(resolution,[status(thm)],[c_32,c_19937])).

tff(c_10791,plain,(
    ! [A_910,B_911,C_912,D_913] :
      ( k8_relset_1(A_910,B_911,C_912,D_913) = k10_relat_1(C_912,D_913)
      | ~ m1_subset_1(C_912,k1_zfmisc_1(k2_zfmisc_1(A_910,B_911))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10794,plain,(
    ! [D_913] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_913) = k10_relat_1('#skF_5',D_913) ),
    inference(resolution,[status(thm)],[c_32,c_10791])).

tff(c_1139,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k8_relset_1(A_301,B_302,C_303,D_304) = k10_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1142,plain,(
    ! [D_304] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_304) = k10_relat_1('#skF_5',D_304) ),
    inference(resolution,[status(thm)],[c_32,c_1139])).

tff(c_54,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_70,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_418,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k8_relset_1(A_195,B_196,C_197,D_198) = k10_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_425,plain,(
    ! [D_198] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_198) = k10_relat_1('#skF_5',D_198) ),
    inference(resolution,[status(thm)],[c_32,c_418])).

tff(c_40,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_373,plain,(
    ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_426,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_373])).

tff(c_24,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k2_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_81,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_24])).

tff(c_89,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_81])).

tff(c_733,plain,(
    ! [A_241,C_242,B_243,D_244] :
      ( r2_hidden(A_241,k10_relat_1(C_242,B_243))
      | ~ r2_hidden(D_244,B_243)
      | ~ r2_hidden(k4_tarski(A_241,D_244),C_242)
      | ~ r2_hidden(D_244,k2_relat_1(C_242))
      | ~ v1_relat_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_827,plain,(
    ! [A_255,C_256] :
      ( r2_hidden(A_255,k10_relat_1(C_256,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_255,'#skF_7'),C_256)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_256))
      | ~ v1_relat_1(C_256) ) ),
    inference(resolution,[status(thm)],[c_64,c_733])).

tff(c_889,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_827])).

tff(c_909,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_89,c_889])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_909])).

tff(c_967,plain,(
    ! [F_263] :
      ( ~ r2_hidden(F_263,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_263),'#skF_5')
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
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1146,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_982])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_16,B_17,C_18),B_17)
      | ~ r2_hidden(A_16,k10_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1247,plain,(
    ! [A_327,B_328,C_329] :
      ( r2_hidden(k4_tarski(A_327,'#skF_1'(A_327,B_328,C_329)),C_329)
      | ~ r2_hidden(A_327,k10_relat_1(C_329,B_328))
      | ~ v1_relat_1(C_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_983,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1082,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_983,c_48])).

tff(c_1254,plain,(
    ! [B_328] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_328,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_328,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_328))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1247,c_1082])).

tff(c_2326,plain,(
    ! [B_458] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_458,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_458,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_458)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1254])).

tff(c_2334,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
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
      ( r2_hidden(k4_tarski(A_509,'#skF_1'(A_509,B_510,C_511)),A_512)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(A_512))
      | ~ r2_hidden(A_509,k10_relat_1(C_511,B_510))
      | ~ v1_relat_1(C_511) ) ),
    inference(resolution,[status(thm)],[c_1247,c_8])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10538,plain,(
    ! [C_866,D_865,C_864,B_867,A_863] :
      ( r2_hidden('#skF_1'(A_863,B_867,C_864),D_865)
      | ~ m1_subset_1(C_864,k1_zfmisc_1(k2_zfmisc_1(C_866,D_865)))
      | ~ r2_hidden(A_863,k10_relat_1(C_864,B_867))
      | ~ v1_relat_1(C_864) ) ),
    inference(resolution,[status(thm)],[c_2807,c_4])).

tff(c_10546,plain,(
    ! [A_863,B_867] :
      ( r2_hidden('#skF_1'(A_863,B_867,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_863,k10_relat_1('#skF_5',B_867))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_10538])).

tff(c_10552,plain,(
    ! [A_868,B_869] :
      ( r2_hidden('#skF_1'(A_868,B_869,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_868,k10_relat_1('#skF_5',B_869)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10546])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10620,plain,(
    ! [A_870,B_871] :
      ( m1_subset_1('#skF_1'(A_870,B_871,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_870,k10_relat_1('#skF_5',B_871)) ) ),
    inference(resolution,[status(thm)],[c_10552,c_10])).

tff(c_10647,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1146,c_10620])).

tff(c_10663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2340,c_10647])).

tff(c_10664,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10797,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10794,c_10664])).

tff(c_10958,plain,(
    ! [A_942,B_943,C_944] :
      ( r2_hidden(k4_tarski(A_942,'#skF_1'(A_942,B_943,C_944)),C_944)
      | ~ r2_hidden(A_942,k10_relat_1(C_944,B_943))
      | ~ v1_relat_1(C_944) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10665,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10738,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10665,c_52])).

tff(c_10972,plain,(
    ! [B_943] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_943,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_943,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_943))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10958,c_10738])).

tff(c_11909,plain,(
    ! [B_1066] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1066,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1066,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_1066)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10972])).

tff(c_11917,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_11909])).

tff(c_11923,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10797,c_11917])).

tff(c_12279,plain,(
    ! [A_1122,B_1123,C_1124,A_1125] :
      ( r2_hidden(k4_tarski(A_1122,'#skF_1'(A_1122,B_1123,C_1124)),A_1125)
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(A_1125))
      | ~ r2_hidden(A_1122,k10_relat_1(C_1124,B_1123))
      | ~ v1_relat_1(C_1124) ) ),
    inference(resolution,[status(thm)],[c_10958,c_8])).

tff(c_19669,plain,(
    ! [C_1477,A_1475,C_1479,B_1478,D_1476] :
      ( r2_hidden('#skF_1'(A_1475,B_1478,C_1479),D_1476)
      | ~ m1_subset_1(C_1479,k1_zfmisc_1(k2_zfmisc_1(C_1477,D_1476)))
      | ~ r2_hidden(A_1475,k10_relat_1(C_1479,B_1478))
      | ~ v1_relat_1(C_1479) ) ),
    inference(resolution,[status(thm)],[c_12279,c_4])).

tff(c_19680,plain,(
    ! [A_1475,B_1478] :
      ( r2_hidden('#skF_1'(A_1475,B_1478,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1475,k10_relat_1('#skF_5',B_1478))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_19669])).

tff(c_19687,plain,(
    ! [A_1480,B_1481] :
      ( r2_hidden('#skF_1'(A_1480,B_1481,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1480,k10_relat_1('#skF_5',B_1481)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_19680])).

tff(c_19752,plain,(
    ! [A_1482,B_1483] :
      ( m1_subset_1('#skF_1'(A_1482,B_1483,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_1482,k10_relat_1('#skF_5',B_1483)) ) ),
    inference(resolution,[status(thm)],[c_19687,c_10])).

tff(c_19775,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10797,c_19752])).

tff(c_19790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11923,c_19775])).

tff(c_19791,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_19947,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19940,c_19791])).

tff(c_19957,plain,(
    ! [A_1541,B_1542,C_1543] :
      ( r2_hidden(k4_tarski(A_1541,'#skF_1'(A_1541,B_1542,C_1543)),C_1543)
      | ~ r2_hidden(A_1541,k10_relat_1(C_1543,B_1542))
      | ~ v1_relat_1(C_1543) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_19792,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_19865,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_19792,c_44])).

tff(c_19964,plain,(
    ! [B_1542] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1542,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1542,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_1542))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_19957,c_19865])).

tff(c_20199,plain,(
    ! [B_1573] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1573,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1573,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_1573)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_19964])).

tff(c_20203,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_20199])).

tff(c_20206,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_19947,c_20203])).

tff(c_20982,plain,(
    ! [A_1686,B_1687,C_1688,A_1689] :
      ( r2_hidden(k4_tarski(A_1686,'#skF_1'(A_1686,B_1687,C_1688)),A_1689)
      | ~ m1_subset_1(C_1688,k1_zfmisc_1(A_1689))
      | ~ r2_hidden(A_1686,k10_relat_1(C_1688,B_1687))
      | ~ v1_relat_1(C_1688) ) ),
    inference(resolution,[status(thm)],[c_19957,c_8])).

tff(c_29060,plain,(
    ! [B_2077,C_2080,D_2078,C_2079,A_2076] :
      ( r2_hidden('#skF_1'(A_2076,B_2077,C_2079),D_2078)
      | ~ m1_subset_1(C_2079,k1_zfmisc_1(k2_zfmisc_1(C_2080,D_2078)))
      | ~ r2_hidden(A_2076,k10_relat_1(C_2079,B_2077))
      | ~ v1_relat_1(C_2079) ) ),
    inference(resolution,[status(thm)],[c_20982,c_4])).

tff(c_29068,plain,(
    ! [A_2076,B_2077] :
      ( r2_hidden('#skF_1'(A_2076,B_2077,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_2076,k10_relat_1('#skF_5',B_2077))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_29060])).

tff(c_29074,plain,(
    ! [A_2081,B_2082] :
      ( r2_hidden('#skF_1'(A_2081,B_2082,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_2081,k10_relat_1('#skF_5',B_2082)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_29068])).

tff(c_29151,plain,(
    ! [A_2083,B_2084] :
      ( m1_subset_1('#skF_1'(A_2083,B_2084,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_2083,k10_relat_1('#skF_5',B_2084)) ) ),
    inference(resolution,[status(thm)],[c_29074,c_10])).

tff(c_29174,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_19947,c_29151])).

tff(c_29193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20206,c_29174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.32/8.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.41/8.99  
% 16.41/8.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.41/8.99  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 16.41/8.99  
% 16.41/8.99  %Foreground sorts:
% 16.41/8.99  
% 16.41/8.99  
% 16.41/8.99  %Background operators:
% 16.41/8.99  
% 16.41/8.99  
% 16.41/8.99  %Foreground operators:
% 16.41/8.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.41/8.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.41/8.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.41/8.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.41/8.99  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 16.41/8.99  tff('#skF_7', type, '#skF_7': $i).
% 16.41/8.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.41/8.99  tff('#skF_5', type, '#skF_5': $i).
% 16.41/8.99  tff('#skF_6', type, '#skF_6': $i).
% 16.41/8.99  tff('#skF_2', type, '#skF_2': $i).
% 16.41/8.99  tff('#skF_3', type, '#skF_3': $i).
% 16.41/8.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.41/8.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.41/8.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.41/8.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.41/8.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.41/8.99  tff('#skF_4', type, '#skF_4': $i).
% 16.41/8.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.41/8.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.41/8.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.41/8.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.41/8.99  
% 16.41/9.02  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.41/9.02  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 16.41/9.02  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 16.41/9.02  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 16.41/9.02  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 16.41/9.02  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 16.41/9.02  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 16.41/9.02  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 16.41/9.02  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 16.41/9.02  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.41/9.02  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_57, plain, (![B_122, A_123]: (v1_relat_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.41/9.02  tff(c_60, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_57])).
% 16.41/9.02  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_60])).
% 16.41/9.02  tff(c_19937, plain, (![A_1536, B_1537, C_1538, D_1539]: (k8_relset_1(A_1536, B_1537, C_1538, D_1539)=k10_relat_1(C_1538, D_1539) | ~m1_subset_1(C_1538, k1_zfmisc_1(k2_zfmisc_1(A_1536, B_1537))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.41/9.02  tff(c_19940, plain, (![D_1539]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_1539)=k10_relat_1('#skF_5', D_1539))), inference(resolution, [status(thm)], [c_32, c_19937])).
% 16.41/9.02  tff(c_10791, plain, (![A_910, B_911, C_912, D_913]: (k8_relset_1(A_910, B_911, C_912, D_913)=k10_relat_1(C_912, D_913) | ~m1_subset_1(C_912, k1_zfmisc_1(k2_zfmisc_1(A_910, B_911))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.41/9.02  tff(c_10794, plain, (![D_913]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_913)=k10_relat_1('#skF_5', D_913))), inference(resolution, [status(thm)], [c_32, c_10791])).
% 16.41/9.02  tff(c_1139, plain, (![A_301, B_302, C_303, D_304]: (k8_relset_1(A_301, B_302, C_303, D_304)=k10_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.41/9.02  tff(c_1142, plain, (![D_304]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_304)=k10_relat_1('#skF_5', D_304))), inference(resolution, [status(thm)], [c_32, c_1139])).
% 16.41/9.02  tff(c_54, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_70, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 16.41/9.02  tff(c_46, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_64, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 16.41/9.02  tff(c_50, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 16.41/9.02  tff(c_418, plain, (![A_195, B_196, C_197, D_198]: (k8_relset_1(A_195, B_196, C_197, D_198)=k10_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.41/9.02  tff(c_425, plain, (![D_198]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_198)=k10_relat_1('#skF_5', D_198))), inference(resolution, [status(thm)], [c_32, c_418])).
% 16.41/9.02  tff(c_40, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_373, plain, (~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 16.41/9.02  tff(c_426, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_373])).
% 16.41/9.02  tff(c_24, plain, (![B_23, C_24, A_22]: (r2_hidden(B_23, k2_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.41/9.02  tff(c_81, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_24])).
% 16.41/9.02  tff(c_89, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_81])).
% 16.41/9.02  tff(c_733, plain, (![A_241, C_242, B_243, D_244]: (r2_hidden(A_241, k10_relat_1(C_242, B_243)) | ~r2_hidden(D_244, B_243) | ~r2_hidden(k4_tarski(A_241, D_244), C_242) | ~r2_hidden(D_244, k2_relat_1(C_242)) | ~v1_relat_1(C_242))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.41/9.02  tff(c_827, plain, (![A_255, C_256]: (r2_hidden(A_255, k10_relat_1(C_256, '#skF_3')) | ~r2_hidden(k4_tarski(A_255, '#skF_7'), C_256) | ~r2_hidden('#skF_7', k2_relat_1(C_256)) | ~v1_relat_1(C_256))), inference(resolution, [status(thm)], [c_64, c_733])).
% 16.41/9.02  tff(c_889, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_827])).
% 16.41/9.02  tff(c_909, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_89, c_889])).
% 16.41/9.02  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_909])).
% 16.41/9.02  tff(c_967, plain, (![F_263]: (~r2_hidden(F_263, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_263), '#skF_5') | ~m1_subset_1(F_263, '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 16.41/9.02  tff(c_974, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_967])).
% 16.41/9.02  tff(c_981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_974])).
% 16.41/9.02  tff(c_982, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 16.41/9.02  tff(c_1146, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_982])).
% 16.41/9.02  tff(c_18, plain, (![A_16, B_17, C_18]: (r2_hidden('#skF_1'(A_16, B_17, C_18), B_17) | ~r2_hidden(A_16, k10_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.41/9.02  tff(c_1247, plain, (![A_327, B_328, C_329]: (r2_hidden(k4_tarski(A_327, '#skF_1'(A_327, B_328, C_329)), C_329) | ~r2_hidden(A_327, k10_relat_1(C_329, B_328)) | ~v1_relat_1(C_329))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.41/9.02  tff(c_983, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 16.41/9.02  tff(c_48, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_1082, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_983, c_48])).
% 16.41/9.02  tff(c_1254, plain, (![B_328]: (~r2_hidden('#skF_1'('#skF_6', B_328, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_328, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_328)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1247, c_1082])).
% 16.41/9.02  tff(c_2326, plain, (![B_458]: (~r2_hidden('#skF_1'('#skF_6', B_458, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_458, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_458)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1254])).
% 16.41/9.02  tff(c_2334, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_2326])).
% 16.41/9.02  tff(c_2340, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1146, c_2334])).
% 16.41/9.02  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.41/9.02  tff(c_2807, plain, (![A_509, B_510, C_511, A_512]: (r2_hidden(k4_tarski(A_509, '#skF_1'(A_509, B_510, C_511)), A_512) | ~m1_subset_1(C_511, k1_zfmisc_1(A_512)) | ~r2_hidden(A_509, k10_relat_1(C_511, B_510)) | ~v1_relat_1(C_511))), inference(resolution, [status(thm)], [c_1247, c_8])).
% 16.41/9.02  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.41/9.02  tff(c_10538, plain, (![C_866, D_865, C_864, B_867, A_863]: (r2_hidden('#skF_1'(A_863, B_867, C_864), D_865) | ~m1_subset_1(C_864, k1_zfmisc_1(k2_zfmisc_1(C_866, D_865))) | ~r2_hidden(A_863, k10_relat_1(C_864, B_867)) | ~v1_relat_1(C_864))), inference(resolution, [status(thm)], [c_2807, c_4])).
% 16.41/9.02  tff(c_10546, plain, (![A_863, B_867]: (r2_hidden('#skF_1'(A_863, B_867, '#skF_5'), '#skF_4') | ~r2_hidden(A_863, k10_relat_1('#skF_5', B_867)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_10538])).
% 16.41/9.02  tff(c_10552, plain, (![A_868, B_869]: (r2_hidden('#skF_1'(A_868, B_869, '#skF_5'), '#skF_4') | ~r2_hidden(A_868, k10_relat_1('#skF_5', B_869)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10546])).
% 16.41/9.02  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.41/9.02  tff(c_10620, plain, (![A_870, B_871]: (m1_subset_1('#skF_1'(A_870, B_871, '#skF_5'), '#skF_4') | ~r2_hidden(A_870, k10_relat_1('#skF_5', B_871)))), inference(resolution, [status(thm)], [c_10552, c_10])).
% 16.41/9.02  tff(c_10647, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1146, c_10620])).
% 16.41/9.02  tff(c_10663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2340, c_10647])).
% 16.41/9.02  tff(c_10664, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 16.41/9.02  tff(c_10797, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10794, c_10664])).
% 16.41/9.02  tff(c_10958, plain, (![A_942, B_943, C_944]: (r2_hidden(k4_tarski(A_942, '#skF_1'(A_942, B_943, C_944)), C_944) | ~r2_hidden(A_942, k10_relat_1(C_944, B_943)) | ~v1_relat_1(C_944))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.41/9.02  tff(c_10665, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 16.41/9.02  tff(c_52, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_10738, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_10665, c_52])).
% 16.41/9.02  tff(c_10972, plain, (![B_943]: (~r2_hidden('#skF_1'('#skF_6', B_943, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_943, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_943)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10958, c_10738])).
% 16.41/9.02  tff(c_11909, plain, (![B_1066]: (~r2_hidden('#skF_1'('#skF_6', B_1066, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_1066, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_1066)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10972])).
% 16.41/9.02  tff(c_11917, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_11909])).
% 16.41/9.02  tff(c_11923, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10797, c_11917])).
% 16.41/9.02  tff(c_12279, plain, (![A_1122, B_1123, C_1124, A_1125]: (r2_hidden(k4_tarski(A_1122, '#skF_1'(A_1122, B_1123, C_1124)), A_1125) | ~m1_subset_1(C_1124, k1_zfmisc_1(A_1125)) | ~r2_hidden(A_1122, k10_relat_1(C_1124, B_1123)) | ~v1_relat_1(C_1124))), inference(resolution, [status(thm)], [c_10958, c_8])).
% 16.41/9.02  tff(c_19669, plain, (![C_1477, A_1475, C_1479, B_1478, D_1476]: (r2_hidden('#skF_1'(A_1475, B_1478, C_1479), D_1476) | ~m1_subset_1(C_1479, k1_zfmisc_1(k2_zfmisc_1(C_1477, D_1476))) | ~r2_hidden(A_1475, k10_relat_1(C_1479, B_1478)) | ~v1_relat_1(C_1479))), inference(resolution, [status(thm)], [c_12279, c_4])).
% 16.41/9.02  tff(c_19680, plain, (![A_1475, B_1478]: (r2_hidden('#skF_1'(A_1475, B_1478, '#skF_5'), '#skF_4') | ~r2_hidden(A_1475, k10_relat_1('#skF_5', B_1478)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_19669])).
% 16.41/9.02  tff(c_19687, plain, (![A_1480, B_1481]: (r2_hidden('#skF_1'(A_1480, B_1481, '#skF_5'), '#skF_4') | ~r2_hidden(A_1480, k10_relat_1('#skF_5', B_1481)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_19680])).
% 16.41/9.02  tff(c_19752, plain, (![A_1482, B_1483]: (m1_subset_1('#skF_1'(A_1482, B_1483, '#skF_5'), '#skF_4') | ~r2_hidden(A_1482, k10_relat_1('#skF_5', B_1483)))), inference(resolution, [status(thm)], [c_19687, c_10])).
% 16.41/9.02  tff(c_19775, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10797, c_19752])).
% 16.41/9.02  tff(c_19790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11923, c_19775])).
% 16.41/9.02  tff(c_19791, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 16.41/9.02  tff(c_19947, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19940, c_19791])).
% 16.41/9.02  tff(c_19957, plain, (![A_1541, B_1542, C_1543]: (r2_hidden(k4_tarski(A_1541, '#skF_1'(A_1541, B_1542, C_1543)), C_1543) | ~r2_hidden(A_1541, k10_relat_1(C_1543, B_1542)) | ~v1_relat_1(C_1543))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.41/9.02  tff(c_19792, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 16.41/9.02  tff(c_44, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.41/9.02  tff(c_19865, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_19792, c_44])).
% 16.41/9.02  tff(c_19964, plain, (![B_1542]: (~r2_hidden('#skF_1'('#skF_6', B_1542, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_1542, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_1542)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_19957, c_19865])).
% 16.41/9.02  tff(c_20199, plain, (![B_1573]: (~r2_hidden('#skF_1'('#skF_6', B_1573, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_1573, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_1573)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_19964])).
% 16.41/9.02  tff(c_20203, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_20199])).
% 16.41/9.02  tff(c_20206, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_19947, c_20203])).
% 16.41/9.02  tff(c_20982, plain, (![A_1686, B_1687, C_1688, A_1689]: (r2_hidden(k4_tarski(A_1686, '#skF_1'(A_1686, B_1687, C_1688)), A_1689) | ~m1_subset_1(C_1688, k1_zfmisc_1(A_1689)) | ~r2_hidden(A_1686, k10_relat_1(C_1688, B_1687)) | ~v1_relat_1(C_1688))), inference(resolution, [status(thm)], [c_19957, c_8])).
% 16.41/9.02  tff(c_29060, plain, (![B_2077, C_2080, D_2078, C_2079, A_2076]: (r2_hidden('#skF_1'(A_2076, B_2077, C_2079), D_2078) | ~m1_subset_1(C_2079, k1_zfmisc_1(k2_zfmisc_1(C_2080, D_2078))) | ~r2_hidden(A_2076, k10_relat_1(C_2079, B_2077)) | ~v1_relat_1(C_2079))), inference(resolution, [status(thm)], [c_20982, c_4])).
% 16.41/9.02  tff(c_29068, plain, (![A_2076, B_2077]: (r2_hidden('#skF_1'(A_2076, B_2077, '#skF_5'), '#skF_4') | ~r2_hidden(A_2076, k10_relat_1('#skF_5', B_2077)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_29060])).
% 16.41/9.02  tff(c_29074, plain, (![A_2081, B_2082]: (r2_hidden('#skF_1'(A_2081, B_2082, '#skF_5'), '#skF_4') | ~r2_hidden(A_2081, k10_relat_1('#skF_5', B_2082)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_29068])).
% 16.41/9.02  tff(c_29151, plain, (![A_2083, B_2084]: (m1_subset_1('#skF_1'(A_2083, B_2084, '#skF_5'), '#skF_4') | ~r2_hidden(A_2083, k10_relat_1('#skF_5', B_2084)))), inference(resolution, [status(thm)], [c_29074, c_10])).
% 16.41/9.02  tff(c_29174, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_19947, c_29151])).
% 16.41/9.02  tff(c_29193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20206, c_29174])).
% 16.41/9.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.41/9.02  
% 16.41/9.02  Inference rules
% 16.41/9.02  ----------------------
% 16.41/9.02  #Ref     : 0
% 16.41/9.02  #Sup     : 8107
% 16.41/9.02  #Fact    : 0
% 16.41/9.02  #Define  : 0
% 16.41/9.02  #Split   : 13
% 16.41/9.02  #Chain   : 0
% 16.41/9.02  #Close   : 0
% 16.41/9.02  
% 16.41/9.02  Ordering : KBO
% 16.41/9.02  
% 16.41/9.02  Simplification rules
% 16.41/9.02  ----------------------
% 16.41/9.02  #Subsume      : 66
% 16.41/9.02  #Demod        : 168
% 16.41/9.02  #Tautology    : 36
% 16.41/9.02  #SimpNegUnit  : 9
% 16.41/9.02  #BackRed      : 15
% 16.41/9.02  
% 16.41/9.02  #Partial instantiations: 0
% 16.41/9.02  #Strategies tried      : 1
% 16.41/9.02  
% 16.41/9.02  Timing (in seconds)
% 16.41/9.02  ----------------------
% 16.41/9.02  Preprocessing        : 0.61
% 16.41/9.02  Parsing              : 0.35
% 16.41/9.02  CNF conversion       : 0.05
% 16.41/9.02  Main loop            : 7.44
% 16.41/9.02  Inferencing          : 1.73
% 16.41/9.02  Reduction            : 1.89
% 16.41/9.02  Demodulation         : 1.27
% 16.41/9.02  BG Simplification    : 0.22
% 16.41/9.02  Subsumption          : 2.96
% 16.41/9.02  Abstraction          : 0.27
% 16.41/9.02  MUC search           : 0.00
% 16.41/9.02  Cooper               : 0.00
% 16.41/9.02  Total                : 8.10
% 16.41/9.02  Index Insertion      : 0.00
% 16.41/9.02  Index Deletion       : 0.00
% 16.41/9.02  Index Matching       : 0.00
% 16.41/9.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
