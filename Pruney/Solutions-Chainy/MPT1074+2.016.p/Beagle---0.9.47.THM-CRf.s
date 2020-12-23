%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  117 (1593 expanded)
%              Number of leaves         :   35 ( 578 expanded)
%              Depth                    :   26
%              Number of atoms          :  247 (5683 expanded)
%              Number of equality atoms :   38 ( 582 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(C,k1_funct_2(A,B))
       => ( k1_relat_1(C) = A
          & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_83,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_83])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_93,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38])).

tff(c_67,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_263,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_xboole_0 = B_101
      | r2_hidden(C_102,k1_funct_2(A_103,B_101))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_101)))
      | ~ v1_funct_2(C_102,A_103,B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_274,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_263])).

tff(c_279,plain,
    ( k1_xboole_0 = '#skF_4'
    | r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_274])).

tff(c_280,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_24,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_relat_1(C_23) = A_21
      | ~ r2_hidden(C_23,k1_funct_2(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_286,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_280,c_24])).

tff(c_295,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_286])).

tff(c_28,plain,(
    ! [C_26,B_25] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_26),B_25,C_26),k1_relat_1(C_26))
      | m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_26),B_25)))
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_303,plain,(
    ! [B_25] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_25,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_25)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_28])).

tff(c_353,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_1'('#skF_3',B_108,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_108))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_295,c_295,c_303])).

tff(c_20,plain,(
    ! [B_19,C_20,A_18] :
      ( k1_xboole_0 = B_19
      | r2_hidden(C_20,k1_funct_2(A_18,B_19))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_356,plain,(
    ! [B_108] :
      ( k1_xboole_0 = B_108
      | r2_hidden('#skF_5',k1_funct_2('#skF_3',B_108))
      | ~ v1_funct_2('#skF_5','#skF_3',B_108)
      | ~ v1_funct_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_108,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_353,c_20])).

tff(c_597,plain,(
    ! [B_134] :
      ( k1_xboole_0 = B_134
      | r2_hidden('#skF_5',k1_funct_2('#skF_3',B_134))
      | ~ v1_funct_2('#skF_5','#skF_3',B_134)
      | r2_hidden('#skF_1'('#skF_3',B_134,'#skF_5'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_356])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_602,plain,(
    ! [B_135] :
      ( m1_subset_1('#skF_1'('#skF_3',B_135,'#skF_5'),'#skF_3')
      | k1_xboole_0 = B_135
      | r2_hidden('#skF_5',k1_funct_2('#skF_3',B_135))
      | ~ v1_funct_2('#skF_5','#skF_3',B_135) ) ),
    inference(resolution,[status(thm)],[c_597,c_4])).

tff(c_22,plain,(
    ! [C_23,B_22,A_21] :
      ( r1_tarski(k2_relat_1(C_23),B_22)
      | ~ r2_hidden(C_23,k1_funct_2(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_605,plain,(
    ! [B_135] :
      ( r1_tarski(k2_relat_1('#skF_5'),B_135)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | m1_subset_1('#skF_1'('#skF_3',B_135,'#skF_5'),'#skF_3')
      | k1_xboole_0 = B_135
      | ~ v1_funct_2('#skF_5','#skF_3',B_135) ) ),
    inference(resolution,[status(thm)],[c_602,c_22])).

tff(c_619,plain,(
    ! [B_136] :
      ( r1_tarski(k2_relat_1('#skF_5'),B_136)
      | m1_subset_1('#skF_1'('#skF_3',B_136,'#skF_5'),'#skF_3')
      | k1_xboole_0 = B_136
      | ~ v1_funct_2('#skF_5','#skF_3',B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_605])).

tff(c_647,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_619,c_93])).

tff(c_649,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_177,plain,(
    ! [C_81,B_82] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_81),B_82,C_81),k1_relat_1(C_81))
      | v1_funct_2(C_81,k1_relat_1(C_81),B_82)
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_181,plain,(
    ! [C_81,B_82] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_81),B_82,C_81),k1_relat_1(C_81))
      | v1_funct_2(C_81,k1_relat_1(C_81),B_82)
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_177,c_4])).

tff(c_312,plain,(
    ! [B_82] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_82,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_82)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_181])).

tff(c_330,plain,(
    ! [B_82] :
      ( m1_subset_1('#skF_1'('#skF_3',B_82,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_295,c_295,c_312])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_407,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k3_funct_2(A_112,B_113,C_114,D_115) = k1_funct_1(C_114,D_115)
      | ~ m1_subset_1(D_115,A_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_2(C_114,A_112,B_113)
      | ~ v1_funct_1(C_114)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_411,plain,(
    ! [B_113,C_114,B_82] :
      ( k3_funct_2('#skF_3',B_113,C_114,'#skF_1'('#skF_3',B_82,'#skF_5')) = k1_funct_1(C_114,'#skF_1'('#skF_3',B_82,'#skF_5'))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_113)))
      | ~ v1_funct_2(C_114,'#skF_3',B_113)
      | ~ v1_funct_1(C_114)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_82) ) ),
    inference(resolution,[status(thm)],[c_330,c_407])).

tff(c_473,plain,(
    ! [B_118,C_119,B_120] :
      ( k3_funct_2('#skF_3',B_118,C_119,'#skF_1'('#skF_3',B_120,'#skF_5')) = k1_funct_1(C_119,'#skF_1'('#skF_3',B_120,'#skF_5'))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_118)))
      | ~ v1_funct_2(C_119,'#skF_3',B_118)
      | ~ v1_funct_1(C_119)
      | v1_funct_2('#skF_5','#skF_3',B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_411])).

tff(c_483,plain,(
    ! [B_120] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_120,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_120,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_120) ) ),
    inference(resolution,[status(thm)],[c_42,c_473])).

tff(c_788,plain,(
    ! [B_147] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_147,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_147,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_483])).

tff(c_40,plain,(
    ! [E_39] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_39),'#skF_2')
      | ~ m1_subset_1(E_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_824,plain,(
    ! [B_153] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_153,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_153,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_40])).

tff(c_30,plain,(
    ! [C_26,B_25] :
      ( ~ r2_hidden(k1_funct_1(C_26,'#skF_1'(k1_relat_1(C_26),B_25,C_26)),B_25)
      | v1_funct_2(C_26,k1_relat_1(C_26),B_25)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_306,plain,(
    ! [B_25] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_25,'#skF_5')),B_25)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_25)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_30])).

tff(c_326,plain,(
    ! [B_25] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_25,'#skF_5')),B_25)
      | v1_funct_2('#skF_5','#skF_3',B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_295,c_306])).

tff(c_832,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_824,c_326])).

tff(c_841,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_649,c_832])).

tff(c_851,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_330,c_841])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_851])).

tff(c_858,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_861,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_858])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k3_funct_2(A_14,B_15,C_16,D_17) = k1_funct_1(C_16,D_17)
      | ~ m1_subset_1(D_17,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_863,plain,(
    ! [B_15,C_16] :
      ( k3_funct_2('#skF_3',B_15,C_16,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_16,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_15)))
      | ~ v1_funct_2(C_16,'#skF_3',B_15)
      | ~ v1_funct_1(C_16)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_861,c_16])).

tff(c_966,plain,(
    ! [B_161,C_162] :
      ( k3_funct_2('#skF_3',B_161,C_162,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_162,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_161)))
      | ~ v1_funct_2(C_162,'#skF_3',B_161)
      | ~ v1_funct_1(C_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_863])).

tff(c_983,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_966])).

tff(c_994,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_983])).

tff(c_1001,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_40])).

tff(c_1007,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_1001])).

tff(c_336,plain,(
    ! [C_104,B_105] :
      ( ~ r2_hidden(k1_funct_1(C_104,'#skF_1'(k1_relat_1(C_104),B_105,C_104)),B_105)
      | m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_104),B_105)))
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_339,plain,(
    ! [B_105] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_105,'#skF_5')),B_105)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_105)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_336])).

tff(c_345,plain,(
    ! [B_105] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_105,'#skF_5')),B_105)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_105))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46,c_295,c_339])).

tff(c_1021,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1007,c_345])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1063,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1021,c_14])).

tff(c_107,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_subset_1(k2_relset_1(A_66,B_67,C_68),k1_zfmisc_1(B_67))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_relset_1(A_66,B_67,C_68),B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(resolution,[status(thm)],[c_107,c_6])).

tff(c_1062,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1021,c_124])).

tff(c_1099,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1062])).

tff(c_1101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1099])).

tff(c_1103,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_858])).

tff(c_437,plain,(
    ! [B_116] :
      ( k2_relset_1('#skF_3',B_116,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_116,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_353,c_14])).

tff(c_441,plain,(
    ! [B_116] :
      ( m1_subset_1('#skF_1'('#skF_3',B_116,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_116,'#skF_5') = k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_437,c_4])).

tff(c_1145,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_441,c_1103])).

tff(c_442,plain,(
    ! [B_117] :
      ( r1_tarski(k2_relset_1('#skF_3',B_117,'#skF_5'),B_117)
      | r2_hidden('#skF_1'('#skF_3',B_117,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_353,c_124])).

tff(c_472,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_1'('#skF_3',B_117,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_117,'#skF_5'),B_117) ) ),
    inference(resolution,[status(thm)],[c_442,c_4])).

tff(c_1151,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_472])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1103,c_1151])).

tff(c_1163,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1172,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_2])).

tff(c_1174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:05:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.69  
% 3.30/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.69  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.30/1.69  
% 3.30/1.69  %Foreground sorts:
% 3.30/1.69  
% 3.30/1.69  
% 3.30/1.69  %Background operators:
% 3.30/1.69  
% 3.30/1.69  
% 3.30/1.69  %Foreground operators:
% 3.30/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.30/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/1.69  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 3.30/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.69  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.30/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.69  
% 3.63/1.71  tff(f_120, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 3.63/1.71  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.63/1.71  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.63/1.71  tff(f_71, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 3.63/1.71  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 3.63/1.71  tff(f_98, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 3.63/1.71  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.63/1.71  tff(f_59, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.63/1.71  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.63/1.71  tff(f_34, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.63/1.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.63/1.71  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_83, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.63/1.71  tff(c_92, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_83])).
% 3.63/1.71  tff(c_38, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_93, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38])).
% 3.63/1.71  tff(c_67, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.63/1.71  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_67])).
% 3.63/1.71  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_263, plain, (![B_101, C_102, A_103]: (k1_xboole_0=B_101 | r2_hidden(C_102, k1_funct_2(A_103, B_101)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_101))) | ~v1_funct_2(C_102, A_103, B_101) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.71  tff(c_274, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_263])).
% 3.63/1.71  tff(c_279, plain, (k1_xboole_0='#skF_4' | r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_274])).
% 3.63/1.71  tff(c_280, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_279])).
% 3.63/1.71  tff(c_24, plain, (![C_23, A_21, B_22]: (k1_relat_1(C_23)=A_21 | ~r2_hidden(C_23, k1_funct_2(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.63/1.71  tff(c_286, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_280, c_24])).
% 3.63/1.71  tff(c_295, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_286])).
% 3.63/1.71  tff(c_28, plain, (![C_26, B_25]: (r2_hidden('#skF_1'(k1_relat_1(C_26), B_25, C_26), k1_relat_1(C_26)) | m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_26), B_25))) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.71  tff(c_303, plain, (![B_25]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_25, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_25))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_28])).
% 3.63/1.71  tff(c_353, plain, (![B_108]: (r2_hidden('#skF_1'('#skF_3', B_108, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_108))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_295, c_295, c_303])).
% 3.63/1.71  tff(c_20, plain, (![B_19, C_20, A_18]: (k1_xboole_0=B_19 | r2_hidden(C_20, k1_funct_2(A_18, B_19)) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.71  tff(c_356, plain, (![B_108]: (k1_xboole_0=B_108 | r2_hidden('#skF_5', k1_funct_2('#skF_3', B_108)) | ~v1_funct_2('#skF_5', '#skF_3', B_108) | ~v1_funct_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_108, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_353, c_20])).
% 3.63/1.71  tff(c_597, plain, (![B_134]: (k1_xboole_0=B_134 | r2_hidden('#skF_5', k1_funct_2('#skF_3', B_134)) | ~v1_funct_2('#skF_5', '#skF_3', B_134) | r2_hidden('#skF_1'('#skF_3', B_134, '#skF_5'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_356])).
% 3.63/1.71  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.63/1.71  tff(c_602, plain, (![B_135]: (m1_subset_1('#skF_1'('#skF_3', B_135, '#skF_5'), '#skF_3') | k1_xboole_0=B_135 | r2_hidden('#skF_5', k1_funct_2('#skF_3', B_135)) | ~v1_funct_2('#skF_5', '#skF_3', B_135))), inference(resolution, [status(thm)], [c_597, c_4])).
% 3.63/1.71  tff(c_22, plain, (![C_23, B_22, A_21]: (r1_tarski(k2_relat_1(C_23), B_22) | ~r2_hidden(C_23, k1_funct_2(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.63/1.71  tff(c_605, plain, (![B_135]: (r1_tarski(k2_relat_1('#skF_5'), B_135) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | m1_subset_1('#skF_1'('#skF_3', B_135, '#skF_5'), '#skF_3') | k1_xboole_0=B_135 | ~v1_funct_2('#skF_5', '#skF_3', B_135))), inference(resolution, [status(thm)], [c_602, c_22])).
% 3.63/1.71  tff(c_619, plain, (![B_136]: (r1_tarski(k2_relat_1('#skF_5'), B_136) | m1_subset_1('#skF_1'('#skF_3', B_136, '#skF_5'), '#skF_3') | k1_xboole_0=B_136 | ~v1_funct_2('#skF_5', '#skF_3', B_136))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_605])).
% 3.63/1.71  tff(c_647, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_619, c_93])).
% 3.63/1.71  tff(c_649, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_647])).
% 3.63/1.71  tff(c_177, plain, (![C_81, B_82]: (r2_hidden('#skF_1'(k1_relat_1(C_81), B_82, C_81), k1_relat_1(C_81)) | v1_funct_2(C_81, k1_relat_1(C_81), B_82) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.71  tff(c_181, plain, (![C_81, B_82]: (m1_subset_1('#skF_1'(k1_relat_1(C_81), B_82, C_81), k1_relat_1(C_81)) | v1_funct_2(C_81, k1_relat_1(C_81), B_82) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_177, c_4])).
% 3.63/1.71  tff(c_312, plain, (![B_82]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_82, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_82) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_181])).
% 3.63/1.71  tff(c_330, plain, (![B_82]: (m1_subset_1('#skF_1'('#skF_3', B_82, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_82))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_295, c_295, c_312])).
% 3.63/1.71  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_407, plain, (![A_112, B_113, C_114, D_115]: (k3_funct_2(A_112, B_113, C_114, D_115)=k1_funct_1(C_114, D_115) | ~m1_subset_1(D_115, A_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_2(C_114, A_112, B_113) | ~v1_funct_1(C_114) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.63/1.71  tff(c_411, plain, (![B_113, C_114, B_82]: (k3_funct_2('#skF_3', B_113, C_114, '#skF_1'('#skF_3', B_82, '#skF_5'))=k1_funct_1(C_114, '#skF_1'('#skF_3', B_82, '#skF_5')) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_113))) | ~v1_funct_2(C_114, '#skF_3', B_113) | ~v1_funct_1(C_114) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_82))), inference(resolution, [status(thm)], [c_330, c_407])).
% 3.63/1.71  tff(c_473, plain, (![B_118, C_119, B_120]: (k3_funct_2('#skF_3', B_118, C_119, '#skF_1'('#skF_3', B_120, '#skF_5'))=k1_funct_1(C_119, '#skF_1'('#skF_3', B_120, '#skF_5')) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_118))) | ~v1_funct_2(C_119, '#skF_3', B_118) | ~v1_funct_1(C_119) | v1_funct_2('#skF_5', '#skF_3', B_120))), inference(negUnitSimplification, [status(thm)], [c_50, c_411])).
% 3.63/1.71  tff(c_483, plain, (![B_120]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_120, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_120, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_120))), inference(resolution, [status(thm)], [c_42, c_473])).
% 3.63/1.71  tff(c_788, plain, (![B_147]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_147, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_147, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_147))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_483])).
% 3.63/1.71  tff(c_40, plain, (![E_39]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_39), '#skF_2') | ~m1_subset_1(E_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.63/1.71  tff(c_824, plain, (![B_153]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_153, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_153, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_153))), inference(superposition, [status(thm), theory('equality')], [c_788, c_40])).
% 3.63/1.71  tff(c_30, plain, (![C_26, B_25]: (~r2_hidden(k1_funct_1(C_26, '#skF_1'(k1_relat_1(C_26), B_25, C_26)), B_25) | v1_funct_2(C_26, k1_relat_1(C_26), B_25) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.71  tff(c_306, plain, (![B_25]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_25, '#skF_5')), B_25) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_25) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_30])).
% 3.63/1.71  tff(c_326, plain, (![B_25]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_25, '#skF_5')), B_25) | v1_funct_2('#skF_5', '#skF_3', B_25))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_295, c_306])).
% 3.63/1.71  tff(c_832, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_824, c_326])).
% 3.63/1.71  tff(c_841, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_649, c_649, c_832])).
% 3.63/1.71  tff(c_851, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_330, c_841])).
% 3.63/1.71  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_851])).
% 3.63/1.71  tff(c_858, plain, (k1_xboole_0='#skF_2' | m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_647])).
% 3.63/1.71  tff(c_861, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_858])).
% 3.63/1.71  tff(c_16, plain, (![A_14, B_15, C_16, D_17]: (k3_funct_2(A_14, B_15, C_16, D_17)=k1_funct_1(C_16, D_17) | ~m1_subset_1(D_17, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.63/1.71  tff(c_863, plain, (![B_15, C_16]: (k3_funct_2('#skF_3', B_15, C_16, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_16, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_15))) | ~v1_funct_2(C_16, '#skF_3', B_15) | ~v1_funct_1(C_16) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_861, c_16])).
% 3.63/1.71  tff(c_966, plain, (![B_161, C_162]: (k3_funct_2('#skF_3', B_161, C_162, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_162, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_161))) | ~v1_funct_2(C_162, '#skF_3', B_161) | ~v1_funct_1(C_162))), inference(negUnitSimplification, [status(thm)], [c_50, c_863])).
% 3.63/1.71  tff(c_983, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_966])).
% 3.63/1.71  tff(c_994, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_983])).
% 3.63/1.71  tff(c_1001, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_994, c_40])).
% 3.63/1.71  tff(c_1007, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_861, c_1001])).
% 3.63/1.71  tff(c_336, plain, (![C_104, B_105]: (~r2_hidden(k1_funct_1(C_104, '#skF_1'(k1_relat_1(C_104), B_105, C_104)), B_105) | m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_104), B_105))) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.71  tff(c_339, plain, (![B_105]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_105, '#skF_5')), B_105) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_105))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_336])).
% 3.63/1.71  tff(c_345, plain, (![B_105]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_105, '#skF_5')), B_105) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_105))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46, c_295, c_339])).
% 3.63/1.71  tff(c_1021, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_1007, c_345])).
% 3.63/1.71  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.63/1.71  tff(c_1063, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1021, c_14])).
% 3.63/1.71  tff(c_107, plain, (![A_66, B_67, C_68]: (m1_subset_1(k2_relset_1(A_66, B_67, C_68), k1_zfmisc_1(B_67)) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.63/1.71  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.63/1.71  tff(c_124, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_relset_1(A_66, B_67, C_68), B_67) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(resolution, [status(thm)], [c_107, c_6])).
% 3.63/1.71  tff(c_1062, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1021, c_124])).
% 3.63/1.71  tff(c_1099, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1062])).
% 3.63/1.71  tff(c_1101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_1099])).
% 3.63/1.71  tff(c_1103, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_858])).
% 3.63/1.71  tff(c_437, plain, (![B_116]: (k2_relset_1('#skF_3', B_116, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_116, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_353, c_14])).
% 3.63/1.71  tff(c_441, plain, (![B_116]: (m1_subset_1('#skF_1'('#skF_3', B_116, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_116, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_437, c_4])).
% 3.63/1.71  tff(c_1145, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_441, c_1103])).
% 3.63/1.71  tff(c_442, plain, (![B_117]: (r1_tarski(k2_relset_1('#skF_3', B_117, '#skF_5'), B_117) | r2_hidden('#skF_1'('#skF_3', B_117, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_353, c_124])).
% 3.63/1.71  tff(c_472, plain, (![B_117]: (m1_subset_1('#skF_1'('#skF_3', B_117, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_117, '#skF_5'), B_117))), inference(resolution, [status(thm)], [c_442, c_4])).
% 3.63/1.71  tff(c_1151, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1145, c_472])).
% 3.63/1.71  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_1103, c_1151])).
% 3.63/1.71  tff(c_1163, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_279])).
% 3.63/1.71  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.63/1.71  tff(c_1172, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_2])).
% 3.63/1.71  tff(c_1174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1172])).
% 3.63/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.71  
% 3.63/1.71  Inference rules
% 3.63/1.71  ----------------------
% 3.63/1.71  #Ref     : 0
% 3.63/1.71  #Sup     : 226
% 3.63/1.71  #Fact    : 0
% 3.63/1.71  #Define  : 0
% 3.63/1.71  #Split   : 6
% 3.63/1.71  #Chain   : 0
% 3.63/1.71  #Close   : 0
% 3.63/1.71  
% 3.63/1.71  Ordering : KBO
% 3.63/1.71  
% 3.63/1.71  Simplification rules
% 3.63/1.71  ----------------------
% 3.63/1.71  #Subsume      : 24
% 3.63/1.71  #Demod        : 169
% 3.63/1.71  #Tautology    : 36
% 3.63/1.71  #SimpNegUnit  : 12
% 3.63/1.71  #BackRed      : 22
% 3.63/1.71  
% 3.63/1.71  #Partial instantiations: 0
% 3.63/1.71  #Strategies tried      : 1
% 3.63/1.71  
% 3.63/1.71  Timing (in seconds)
% 3.63/1.71  ----------------------
% 3.63/1.71  Preprocessing        : 0.35
% 3.63/1.72  Parsing              : 0.17
% 3.63/1.72  CNF conversion       : 0.02
% 3.63/1.72  Main loop            : 0.53
% 3.63/1.72  Inferencing          : 0.19
% 3.63/1.72  Reduction            : 0.17
% 3.63/1.72  Demodulation         : 0.12
% 3.63/1.72  BG Simplification    : 0.03
% 3.63/1.72  Subsumption          : 0.09
% 3.63/1.72  Abstraction          : 0.04
% 3.63/1.72  MUC search           : 0.00
% 3.63/1.72  Cooper               : 0.00
% 3.63/1.72  Total                : 0.94
% 3.63/1.72  Index Insertion      : 0.00
% 3.63/1.72  Index Deletion       : 0.00
% 3.63/1.72  Index Matching       : 0.00
% 3.63/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
