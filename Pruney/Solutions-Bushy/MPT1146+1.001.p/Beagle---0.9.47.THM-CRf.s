%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1146+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:29 EST 2020

% Result     : Theorem 18.04s
% Output     : CNFRefutation 18.30s
% Verified   : 
% Statistics : Number of formulae       :  360 (5949 expanded)
%              Number of leaves         :   46 (1777 expanded)
%              Depth                    :   23
%              Number of atoms          :  821 (30607 expanded)
%              Number of equality atoms :   87 ( 950 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > v6_orders_2 > r7_relat_2 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ~ ( ? [D] :
                          ( v6_orders_2(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                          & r2_hidden(B,D)
                          & r2_hidden(C,D) )
                      & ~ r1_orders_2(A,B,C)
                      & ~ r1_orders_2(A,C,B) )
                  & ~ ( ( r1_orders_2(A,B,C)
                        | r1_orders_2(A,C,B) )
                      & ! [D] :
                          ( ( v6_orders_2(D,A)
                            & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                         => ~ ( r2_hidden(B,D)
                              & r2_hidden(C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_157,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v6_orders_2(k7_domain_1(u1_struct_0(A),B,C),A)
                  & m1_subset_1(k7_domain_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(A))) )
              <=> ( r3_orders_2(A,B,C)
                  | r3_orders_2(A,C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_orders_2)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

tff(c_74,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,(
    ! [A_48] :
      ( v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | ~ v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58971,plain,(
    ! [A_90041] :
      ( m1_subset_1(u1_orders_2(A_90041),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_90041),u1_struct_0(A_90041))))
      | ~ l1_orders_2(A_90041) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_58979,plain,(
    ! [A_90041] :
      ( v1_relat_1(u1_orders_2(A_90041))
      | ~ l1_orders_2(A_90041) ) ),
    inference(resolution,[status(thm)],[c_58971,c_2])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_59004,plain,(
    ! [A_90053,B_90054,C_90055] :
      ( k7_domain_1(A_90053,B_90054,C_90055) = k2_tarski(B_90054,C_90055)
      | ~ m1_subset_1(C_90055,A_90053)
      | ~ m1_subset_1(B_90054,A_90053)
      | v1_xboole_0(A_90053) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_59015,plain,(
    ! [B_90054] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_90054,'#skF_7') = k2_tarski(B_90054,'#skF_7')
      | ~ m1_subset_1(B_90054,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_59004])).

tff(c_59044,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_59015])).

tff(c_4,plain,(
    ! [C_7,B_5,A_4] :
      ( v1_xboole_0(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(B_5,A_4)))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58978,plain,(
    ! [A_90041] :
      ( v1_xboole_0(u1_orders_2(A_90041))
      | ~ v1_xboole_0(u1_struct_0(A_90041))
      | ~ l1_orders_2(A_90041) ) ),
    inference(resolution,[status(thm)],[c_58971,c_4])).

tff(c_59047,plain,
    ( v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_59044,c_58978])).

tff(c_59050,plain,(
    v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_59047])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_51799,plain,(
    ! [A_78657,B_78658,C_78659] :
      ( k7_domain_1(A_78657,B_78658,C_78659) = k2_tarski(B_78658,C_78659)
      | ~ m1_subset_1(C_78659,A_78657)
      | ~ m1_subset_1(B_78658,A_78657)
      | v1_xboole_0(A_78657) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_51810,plain,(
    ! [B_78658] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_78658,'#skF_7') = k2_tarski(B_78658,'#skF_7')
      | ~ m1_subset_1(B_78658,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_51799])).

tff(c_51813,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_51810])).

tff(c_28450,plain,(
    ! [A_43815] :
      ( m1_subset_1(u1_orders_2(A_43815),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43815),u1_struct_0(A_43815))))
      | ~ l1_orders_2(A_43815) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28457,plain,(
    ! [A_43815] :
      ( v1_xboole_0(u1_orders_2(A_43815))
      | ~ v1_xboole_0(u1_struct_0(A_43815))
      | ~ l1_orders_2(A_43815) ) ),
    inference(resolution,[status(thm)],[c_28450,c_4])).

tff(c_51817,plain,
    ( v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_51813,c_28457])).

tff(c_51820,plain,(
    v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_51817])).

tff(c_21831,plain,(
    ! [A_33121,B_33122,C_33123] :
      ( k7_domain_1(A_33121,B_33122,C_33123) = k2_tarski(B_33122,C_33123)
      | ~ m1_subset_1(C_33123,A_33121)
      | ~ m1_subset_1(B_33122,A_33121)
      | v1_xboole_0(A_33121) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_21842,plain,(
    ! [B_33122] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_33122,'#skF_7') = k2_tarski(B_33122,'#skF_7')
      | ~ m1_subset_1(B_33122,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_21831])).

tff(c_21845,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_21842])).

tff(c_238,plain,(
    ! [A_113] :
      ( m1_subset_1(u1_orders_2(A_113),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_113),u1_struct_0(A_113))))
      | ~ l1_orders_2(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_245,plain,(
    ! [A_113] :
      ( v1_xboole_0(u1_orders_2(A_113))
      | ~ v1_xboole_0(u1_struct_0(A_113))
      | ~ l1_orders_2(A_113) ) ),
    inference(resolution,[status(thm)],[c_238,c_4])).

tff(c_21848,plain,
    ( v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_21845,c_245])).

tff(c_21851,plain,(
    v1_xboole_0(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_21848])).

tff(c_100,plain,
    ( v6_orders_2('#skF_8','#skF_5')
    | r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_114,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_25002,plain,(
    ! [B_37330,C_37331,A_37332] :
      ( r2_hidden(k4_tarski(B_37330,C_37331),u1_orders_2(A_37332))
      | ~ r1_orders_2(A_37332,B_37330,C_37331)
      | ~ m1_subset_1(C_37331,u1_struct_0(A_37332))
      | ~ m1_subset_1(B_37330,u1_struct_0(A_37332))
      | ~ l1_orders_2(A_37332) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [B_63,A_62] :
      ( ~ v1_xboole_0(B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_25240,plain,(
    ! [A_37468,B_37469,C_37470] :
      ( ~ v1_xboole_0(u1_orders_2(A_37468))
      | ~ r1_orders_2(A_37468,B_37469,C_37470)
      | ~ m1_subset_1(C_37470,u1_struct_0(A_37468))
      | ~ m1_subset_1(B_37469,u1_struct_0(A_37468))
      | ~ l1_orders_2(A_37468) ) ),
    inference(resolution,[status(thm)],[c_25002,c_68])).

tff(c_25242,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_25240])).

tff(c_25246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_21851,c_25242])).

tff(c_25248,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_21842])).

tff(c_25252,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_25248])).

tff(c_25253,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_25252])).

tff(c_16,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_25254,plain,(
    ! [B_37537] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_37537,'#skF_7') = k2_tarski(B_37537,'#skF_7')
      | ~ m1_subset_1(B_37537,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_21842])).

tff(c_25262,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_25254])).

tff(c_44,plain,(
    ! [A_43,B_44,C_45] :
      ( m1_subset_1(k7_domain_1(A_43,B_44,C_45),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(C_45,A_43)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_25800,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25262,c_44])).

tff(c_25820,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_25800])).

tff(c_25821,plain,(
    m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_25248,c_25820])).

tff(c_80,plain,(
    ! [D_82] :
      ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
      | ~ r2_hidden('#skF_7',D_82)
      | ~ r2_hidden('#skF_6',D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v6_orders_2(D_82,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_21800,plain,(
    ! [D_82] :
      ( ~ r2_hidden('#skF_7',D_82)
      | ~ r2_hidden('#skF_6',D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v6_orders_2(D_82,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_80])).

tff(c_25830,plain,
    ( ~ r2_hidden('#skF_7',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_hidden('#skF_6',k2_tarski('#skF_6','#skF_7'))
    | ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_25821,c_21800])).

tff(c_25881,plain,(
    ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_25830])).

tff(c_76,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_28117,plain,(
    ! [A_42922,B_42923,C_42924] :
      ( r3_orders_2(A_42922,B_42923,C_42924)
      | ~ r1_orders_2(A_42922,B_42923,C_42924)
      | ~ m1_subset_1(C_42924,u1_struct_0(A_42922))
      | ~ m1_subset_1(B_42923,u1_struct_0(A_42922))
      | ~ l1_orders_2(A_42922)
      | ~ v3_orders_2(A_42922)
      | v2_struct_0(A_42922) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_28122,plain,(
    ! [B_42923] :
      ( r3_orders_2('#skF_5',B_42923,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_42923,'#skF_7')
      | ~ m1_subset_1(B_42923,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_28117])).

tff(c_28127,plain,(
    ! [B_42923] :
      ( r3_orders_2('#skF_5',B_42923,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_42923,'#skF_7')
      | ~ m1_subset_1(B_42923,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_28122])).

tff(c_28133,plain,(
    ! [B_42991] :
      ( r3_orders_2('#skF_5',B_42991,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_42991,'#skF_7')
      | ~ m1_subset_1(B_42991,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25253,c_28127])).

tff(c_28139,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_28133])).

tff(c_28143,plain,(
    r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_28139])).

tff(c_28260,plain,(
    ! [A_43725,B_43726,C_43727] :
      ( ~ r3_orders_2(A_43725,B_43726,C_43727)
      | v6_orders_2(k7_domain_1(u1_struct_0(A_43725),B_43726,C_43727),A_43725)
      | ~ m1_subset_1(C_43727,u1_struct_0(A_43725))
      | ~ m1_subset_1(B_43726,u1_struct_0(A_43725))
      | ~ l1_orders_2(A_43725)
      | ~ v3_orders_2(A_43725)
      | v2_struct_0(A_43725) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_28285,plain,
    ( ~ r3_orders_2('#skF_5','#skF_6','#skF_7')
    | v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25262,c_28260])).

tff(c_28310,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_28143,c_28285])).

tff(c_28312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25253,c_25881,c_28310])).

tff(c_28313,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_25252])).

tff(c_28317,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_28313])).

tff(c_28321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_28317])).

tff(c_28323,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_94,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_28377,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_28323,c_94])).

tff(c_28378,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_28377])).

tff(c_53942,plain,(
    ! [B_82456,C_82457,A_82458] :
      ( r2_hidden(k4_tarski(B_82456,C_82457),u1_orders_2(A_82458))
      | ~ r1_orders_2(A_82458,B_82456,C_82457)
      | ~ m1_subset_1(C_82457,u1_struct_0(A_82458))
      | ~ m1_subset_1(B_82456,u1_struct_0(A_82458))
      | ~ l1_orders_2(A_82458) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54932,plain,(
    ! [A_82938,B_82939,C_82940] :
      ( ~ v1_xboole_0(u1_orders_2(A_82938))
      | ~ r1_orders_2(A_82938,B_82939,C_82940)
      | ~ m1_subset_1(C_82940,u1_struct_0(A_82938))
      | ~ m1_subset_1(B_82939,u1_struct_0(A_82938))
      | ~ l1_orders_2(A_82938) ) ),
    inference(resolution,[status(thm)],[c_53942,c_68])).

tff(c_54934,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28378,c_54932])).

tff(c_54938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_72,c_51820,c_54934])).

tff(c_54940,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_51810])).

tff(c_54944,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_54940])).

tff(c_54945,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54944])).

tff(c_54956,plain,(
    ! [B_83008] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_83008,'#skF_7') = k2_tarski(B_83008,'#skF_7')
      | ~ m1_subset_1(B_83008,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_51810])).

tff(c_54964,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_54956])).

tff(c_54997,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54964,c_44])).

tff(c_55001,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_54997])).

tff(c_55002,plain,(
    m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54940,c_55001])).

tff(c_78,plain,(
    ! [D_82] :
      ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
      | ~ r2_hidden('#skF_7',D_82)
      | ~ r2_hidden('#skF_6',D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v6_orders_2(D_82,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_54947,plain,(
    ! [D_82] :
      ( ~ r2_hidden('#skF_7',D_82)
      | ~ r2_hidden('#skF_6',D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v6_orders_2(D_82,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28378,c_78])).

tff(c_55007,plain,
    ( ~ r2_hidden('#skF_7',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_hidden('#skF_6',k2_tarski('#skF_6','#skF_7'))
    | ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_55002,c_54947])).

tff(c_55018,plain,(
    ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_55007])).

tff(c_58679,plain,(
    ! [A_89483,B_89484,C_89485] :
      ( r3_orders_2(A_89483,B_89484,C_89485)
      | ~ r1_orders_2(A_89483,B_89484,C_89485)
      | ~ m1_subset_1(C_89485,u1_struct_0(A_89483))
      | ~ m1_subset_1(B_89484,u1_struct_0(A_89483))
      | ~ l1_orders_2(A_89483)
      | ~ v3_orders_2(A_89483)
      | v2_struct_0(A_89483) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58686,plain,(
    ! [B_89484] :
      ( r3_orders_2('#skF_5',B_89484,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_89484,'#skF_6')
      | ~ m1_subset_1(B_89484,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_58679])).

tff(c_58693,plain,(
    ! [B_89484] :
      ( r3_orders_2('#skF_5',B_89484,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_89484,'#skF_6')
      | ~ m1_subset_1(B_89484,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58686])).

tff(c_58809,plain,(
    ! [B_89820] :
      ( r3_orders_2('#skF_5',B_89820,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_89820,'#skF_6')
      | ~ m1_subset_1(B_89820,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54945,c_58693])).

tff(c_58812,plain,
    ( r3_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_58809])).

tff(c_58818,plain,(
    r3_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28378,c_58812])).

tff(c_6,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51811,plain,(
    ! [B_78658] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_78658,'#skF_6') = k2_tarski(B_78658,'#skF_6')
      | ~ m1_subset_1(B_78658,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_72,c_51799])).

tff(c_56224,plain,(
    ! [B_85396] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_85396,'#skF_6') = k2_tarski(B_85396,'#skF_6')
      | ~ m1_subset_1(B_85396,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54940,c_51811])).

tff(c_56257,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_56224])).

tff(c_56262,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56257])).

tff(c_58827,plain,(
    ! [A_89953,B_89954,C_89955] :
      ( ~ r3_orders_2(A_89953,B_89954,C_89955)
      | v6_orders_2(k7_domain_1(u1_struct_0(A_89953),B_89954,C_89955),A_89953)
      | ~ m1_subset_1(C_89955,u1_struct_0(A_89953))
      | ~ m1_subset_1(B_89954,u1_struct_0(A_89953))
      | ~ l1_orders_2(A_89953)
      | ~ v3_orders_2(A_89953)
      | v2_struct_0(A_89953) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58847,plain,
    ( ~ r3_orders_2('#skF_5','#skF_7','#skF_6')
    | v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_56262,c_58827])).

tff(c_58874,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_72,c_58818,c_58847])).

tff(c_58876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54945,c_55018,c_58874])).

tff(c_58877,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_54944])).

tff(c_58881,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_58877])).

tff(c_58885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58881])).

tff(c_58887,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28377])).

tff(c_28322,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | v6_orders_2('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_58901,plain,(
    v6_orders_2('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58887,c_28322])).

tff(c_98,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_58921,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_28323,c_58887,c_98])).

tff(c_58988,plain,(
    ! [A_90045,B_90046] :
      ( r7_relat_2(u1_orders_2(A_90045),B_90046)
      | ~ v6_orders_2(B_90046,A_90045)
      | ~ m1_subset_1(B_90046,k1_zfmisc_1(u1_struct_0(A_90045)))
      | ~ l1_orders_2(A_90045) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58991,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),'#skF_8')
    | ~ v6_orders_2('#skF_8','#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_58921,c_58988])).

tff(c_58994,plain,(
    r7_relat_2(u1_orders_2('#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58901,c_58991])).

tff(c_96,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_58892,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_28323,c_96])).

tff(c_58893,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58892])).

tff(c_58894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58887,c_58893])).

tff(c_58895,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_58892])).

tff(c_62849,plain,(
    ! [D_95016,C_95017,A_95018,B_95019] :
      ( r2_hidden(k4_tarski(D_95016,C_95017),A_95018)
      | r2_hidden(k4_tarski(C_95017,D_95016),A_95018)
      | ~ r2_hidden(D_95016,B_95019)
      | ~ r2_hidden(C_95017,B_95019)
      | ~ r7_relat_2(A_95018,B_95019)
      | ~ v1_relat_1(A_95018) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62882,plain,(
    ! [C_95017,A_95018] :
      ( r2_hidden(k4_tarski('#skF_6',C_95017),A_95018)
      | r2_hidden(k4_tarski(C_95017,'#skF_6'),A_95018)
      | ~ r2_hidden(C_95017,'#skF_8')
      | ~ r7_relat_2(A_95018,'#skF_8')
      | ~ v1_relat_1(A_95018) ) ),
    inference(resolution,[status(thm)],[c_58895,c_62849])).

tff(c_63037,plain,(
    ! [A_95018] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | ~ r7_relat_2(A_95018,'#skF_8')
      | ~ v1_relat_1(A_95018)
      | r2_hidden(k4_tarski('#skF_6','#skF_6'),A_95018) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_62882])).

tff(c_63109,plain,(
    ! [A_95222] :
      ( ~ r7_relat_2(A_95222,'#skF_8')
      | ~ v1_relat_1(A_95222)
      | r2_hidden(k4_tarski('#skF_6','#skF_6'),A_95222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58895,c_63037])).

tff(c_63142,plain,(
    ! [A_95289] :
      ( ~ v1_xboole_0(A_95289)
      | ~ r7_relat_2(A_95289,'#skF_8')
      | ~ v1_relat_1(A_95289) ) ),
    inference(resolution,[status(thm)],[c_63109,c_68])).

tff(c_63145,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58994,c_63142])).

tff(c_63152,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59050,c_63145])).

tff(c_63156,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_58979,c_63152])).

tff(c_63160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_63156])).

tff(c_63162,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_59015])).

tff(c_63166,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_63162])).

tff(c_63167,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_63166])).

tff(c_74551,plain,(
    ! [D_115588,C_115589,A_115590,B_115591] :
      ( r2_hidden(k4_tarski(D_115588,C_115589),A_115590)
      | r2_hidden(k4_tarski(C_115589,D_115588),A_115590)
      | ~ r2_hidden(D_115588,B_115591)
      | ~ r2_hidden(C_115589,B_115591)
      | ~ r7_relat_2(A_115590,B_115591)
      | ~ v1_relat_1(A_115590) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_74584,plain,(
    ! [C_115589,A_115590] :
      ( r2_hidden(k4_tarski('#skF_6',C_115589),A_115590)
      | r2_hidden(k4_tarski(C_115589,'#skF_6'),A_115590)
      | ~ r2_hidden(C_115589,'#skF_8')
      | ~ r7_relat_2(A_115590,'#skF_8')
      | ~ v1_relat_1(A_115590) ) ),
    inference(resolution,[status(thm)],[c_58895,c_74551])).

tff(c_74663,plain,(
    ! [A_115590] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | ~ r7_relat_2(A_115590,'#skF_8')
      | ~ v1_relat_1(A_115590)
      | r2_hidden(k4_tarski('#skF_6','#skF_6'),A_115590) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_74584])).

tff(c_74721,plain,(
    ! [A_115932] :
      ( ~ r7_relat_2(A_115932,'#skF_8')
      | ~ v1_relat_1(A_115932)
      | r2_hidden(k4_tarski('#skF_6','#skF_6'),A_115932) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58895,c_74663])).

tff(c_74747,plain,(
    ! [A_115999] :
      ( ~ v1_xboole_0(A_115999)
      | ~ r7_relat_2(A_115999,'#skF_8')
      | ~ v1_relat_1(A_115999) ) ),
    inference(resolution,[status(thm)],[c_74721,c_68])).

tff(c_74755,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58994,c_74747])).

tff(c_74757,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_74755])).

tff(c_74760,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_58979,c_74757])).

tff(c_74764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74760])).

tff(c_74766,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74755])).

tff(c_58956,plain,(
    ! [A_90039,B_90040] :
      ( r2_hidden('#skF_3'(A_90039,B_90040),B_90040)
      | r7_relat_2(A_90039,B_90040)
      | ~ v1_relat_1(A_90039) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [D_18,B_14,A_13] :
      ( D_18 = B_14
      | D_18 = A_13
      | ~ r2_hidden(D_18,k2_tarski(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104572,plain,(
    ! [A_144879,A_144880,B_144881] :
      ( '#skF_3'(A_144879,k2_tarski(A_144880,B_144881)) = B_144881
      | '#skF_3'(A_144879,k2_tarski(A_144880,B_144881)) = A_144880
      | r7_relat_2(A_144879,k2_tarski(A_144880,B_144881))
      | ~ v1_relat_1(A_144879) ) ),
    inference(resolution,[status(thm)],[c_58956,c_12])).

tff(c_63169,plain,(
    ! [B_95425] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_95425,'#skF_7') = k2_tarski(B_95425,'#skF_7')
      | ~ m1_subset_1(B_95425,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_59015])).

tff(c_63177,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_63169])).

tff(c_63205,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_63177,c_44])).

tff(c_63209,plain,
    ( m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_63205])).

tff(c_63210,plain,(
    m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_63162,c_63209])).

tff(c_8,plain,(
    ! [B_12,A_10] :
      ( v6_orders_2(B_12,A_10)
      | ~ r7_relat_2(u1_orders_2(A_10),B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63216,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_63210,c_8])).

tff(c_63223,plain,
    ( v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_63216])).

tff(c_67432,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_63223])).

tff(c_104575,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_104572,c_67432])).

tff(c_104949,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_104575])).

tff(c_104950,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_104949])).

tff(c_58939,plain,(
    ! [A_90032,B_90033] :
      ( r2_hidden('#skF_4'(A_90032,B_90033),B_90033)
      | r7_relat_2(A_90032,B_90033)
      | ~ v1_relat_1(A_90032) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_85432,plain,(
    ! [A_127370,A_127371,B_127372] :
      ( '#skF_4'(A_127370,k2_tarski(A_127371,B_127372)) = B_127372
      | '#skF_4'(A_127370,k2_tarski(A_127371,B_127372)) = A_127371
      | r7_relat_2(A_127370,k2_tarski(A_127371,B_127372))
      | ~ v1_relat_1(A_127370) ) ),
    inference(resolution,[status(thm)],[c_58939,c_12])).

tff(c_85435,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_85432,c_67432])).

tff(c_85745,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_85435])).

tff(c_85746,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_85745])).

tff(c_10,plain,(
    ! [A_10,B_12] :
      ( r7_relat_2(u1_orders_2(A_10),B_12)
      | ~ v6_orders_2(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63219,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_63210,c_10])).

tff(c_63226,plain,
    ( r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_63219])).

tff(c_67437,plain,(
    ~ v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_63226])).

tff(c_59016,plain,(
    ! [B_90054] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_90054,'#skF_6') = k2_tarski(B_90054,'#skF_6')
      | ~ m1_subset_1(B_90054,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_72,c_59004])).

tff(c_67441,plain,(
    ! [B_103631] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_103631,'#skF_6') = k2_tarski(B_103631,'#skF_6')
      | ~ m1_subset_1(B_103631,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63162,c_59016])).

tff(c_67444,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_67441])).

tff(c_67449,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_67444])).

tff(c_78006,plain,(
    ! [A_119844,C_119845,B_119846] :
      ( ~ r3_orders_2(A_119844,C_119845,B_119846)
      | v6_orders_2(k7_domain_1(u1_struct_0(A_119844),B_119846,C_119845),A_119844)
      | ~ m1_subset_1(C_119845,u1_struct_0(A_119844))
      | ~ m1_subset_1(B_119846,u1_struct_0(A_119844))
      | ~ l1_orders_2(A_119844)
      | ~ v3_orders_2(A_119844)
      | v2_struct_0(A_119844) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_78018,plain,
    ( ~ r3_orders_2('#skF_5','#skF_6','#skF_7')
    | v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_67449,c_78006])).

tff(c_78029,plain,
    ( ~ r3_orders_2('#skF_5','#skF_6','#skF_7')
    | v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_72,c_78018])).

tff(c_78030,plain,(
    ~ r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_67437,c_78029])).

tff(c_93372,plain,(
    ! [A_133857,A_133858,B_133859] :
      ( '#skF_3'(A_133857,k2_tarski(A_133858,B_133859)) = B_133859
      | '#skF_3'(A_133857,k2_tarski(A_133858,B_133859)) = A_133858
      | r7_relat_2(A_133857,k2_tarski(A_133858,B_133859))
      | ~ v1_relat_1(A_133857) ) ),
    inference(resolution,[status(thm)],[c_58956,c_12])).

tff(c_93375,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_93372,c_67432])).

tff(c_93749,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_93375])).

tff(c_93750,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_93749])).

tff(c_74934,plain,(
    ! [A_116606,B_116607,C_116608] :
      ( r3_orders_2(A_116606,B_116607,C_116608)
      | ~ r1_orders_2(A_116606,B_116607,C_116608)
      | ~ m1_subset_1(C_116608,u1_struct_0(A_116606))
      | ~ m1_subset_1(B_116607,u1_struct_0(A_116606))
      | ~ l1_orders_2(A_116606)
      | ~ v3_orders_2(A_116606)
      | v2_struct_0(A_116606) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_74939,plain,(
    ! [B_116607] :
      ( r3_orders_2('#skF_5',B_116607,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_116607,'#skF_7')
      | ~ m1_subset_1(B_116607,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_74934])).

tff(c_74944,plain,(
    ! [B_116607] :
      ( r3_orders_2('#skF_5',B_116607,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_116607,'#skF_7')
      | ~ m1_subset_1(B_116607,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_74939])).

tff(c_74950,plain,(
    ! [B_116675] :
      ( r3_orders_2('#skF_5',B_116675,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_116675,'#skF_7')
      | ~ m1_subset_1(B_116675,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_74944])).

tff(c_74957,plain,
    ( r3_orders_2('#skF_5','#skF_7','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_74950])).

tff(c_74959,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74957])).

tff(c_58886,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_28377])).

tff(c_74585,plain,(
    ! [C_115589,A_115590] :
      ( r2_hidden(k4_tarski('#skF_7',C_115589),A_115590)
      | r2_hidden(k4_tarski(C_115589,'#skF_7'),A_115590)
      | ~ r2_hidden(C_115589,'#skF_8')
      | ~ r7_relat_2(A_115590,'#skF_8')
      | ~ v1_relat_1(A_115590) ) ),
    inference(resolution,[status(thm)],[c_58886,c_74551])).

tff(c_74785,plain,(
    ! [A_115590] :
      ( ~ r2_hidden('#skF_7','#skF_8')
      | ~ r7_relat_2(A_115590,'#skF_8')
      | ~ v1_relat_1(A_115590)
      | r2_hidden(k4_tarski('#skF_7','#skF_7'),A_115590) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_74585])).

tff(c_74843,plain,(
    ! [A_116401] :
      ( ~ r7_relat_2(A_116401,'#skF_8')
      | ~ v1_relat_1(A_116401)
      | r2_hidden(k4_tarski('#skF_7','#skF_7'),A_116401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58886,c_74785])).

tff(c_40,plain,(
    ! [A_36,B_40,C_42] :
      ( r1_orders_2(A_36,B_40,C_42)
      | ~ r2_hidden(k4_tarski(B_40,C_42),u1_orders_2(A_36))
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_subset_1(B_40,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76015,plain,(
    ! [A_117754] :
      ( r1_orders_2(A_117754,'#skF_7','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_117754))
      | ~ l1_orders_2(A_117754)
      | ~ r7_relat_2(u1_orders_2(A_117754),'#skF_8')
      | ~ v1_relat_1(u1_orders_2(A_117754)) ) ),
    inference(resolution,[status(thm)],[c_74843,c_40])).

tff(c_76021,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58994,c_76015])).

tff(c_76027,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_74,c_70,c_76021])).

tff(c_76029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74959,c_76027])).

tff(c_76031,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74957])).

tff(c_74941,plain,(
    ! [B_116607] :
      ( r3_orders_2('#skF_5',B_116607,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_116607,'#skF_6')
      | ~ m1_subset_1(B_116607,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_74934])).

tff(c_74948,plain,(
    ! [B_116607] :
      ( r3_orders_2('#skF_5',B_116607,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_116607,'#skF_6')
      | ~ m1_subset_1(B_116607,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_74941])).

tff(c_76043,plain,(
    ! [B_117953] :
      ( r3_orders_2('#skF_5',B_117953,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_117953,'#skF_6')
      | ~ m1_subset_1(B_117953,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_74948])).

tff(c_76051,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_76043])).

tff(c_76052,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76051])).

tff(c_77298,plain,(
    ! [A_119304] :
      ( r1_orders_2(A_119304,'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_119304))
      | ~ l1_orders_2(A_119304)
      | ~ r7_relat_2(u1_orders_2(A_119304),'#skF_8')
      | ~ v1_relat_1(u1_orders_2(A_119304)) ) ),
    inference(resolution,[status(thm)],[c_74721,c_40])).

tff(c_77304,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58994,c_77298])).

tff(c_77310,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_74,c_72,c_77304])).

tff(c_77312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76052,c_77310])).

tff(c_77314,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76051])).

tff(c_89446,plain,(
    ! [A_129405,A_129406,B_129407] :
      ( '#skF_3'(A_129405,k2_tarski(A_129406,B_129407)) = B_129407
      | '#skF_3'(A_129405,k2_tarski(A_129406,B_129407)) = A_129406
      | r7_relat_2(A_129405,k2_tarski(A_129406,B_129407))
      | ~ v1_relat_1(A_129405) ) ),
    inference(resolution,[status(thm)],[c_58956,c_12])).

tff(c_89449,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_89446,c_67432])).

tff(c_89759,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_89449])).

tff(c_89760,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_89759])).

tff(c_86360,plain,(
    ! [A_128167,A_128168,B_128169] :
      ( '#skF_3'(A_128167,k2_tarski(A_128168,B_128169)) = B_128169
      | '#skF_3'(A_128167,k2_tarski(A_128168,B_128169)) = A_128168
      | r7_relat_2(A_128167,k2_tarski(A_128168,B_128169))
      | ~ v1_relat_1(A_128167) ) ),
    inference(resolution,[status(thm)],[c_58956,c_12])).

tff(c_86363,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_86360,c_67432])).

tff(c_86676,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_86363])).

tff(c_86677,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_86676])).

tff(c_42,plain,(
    ! [B_40,C_42,A_36] :
      ( r2_hidden(k4_tarski(B_40,C_42),u1_orders_2(A_36))
      | ~ r1_orders_2(A_36,B_40,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_subset_1(B_40,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_19,B_29),'#skF_4'(A_19,B_29)),A_19)
      | r7_relat_2(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_85750,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_85746,c_34])).

tff(c_85909,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_85750])).

tff(c_85910,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_85909])).

tff(c_85939,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_85910])).

tff(c_85960,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_85939])).

tff(c_85998,plain,(
    ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_85960])).

tff(c_86678,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86677,c_85998])).

tff(c_86683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_86678])).

tff(c_86684,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_86676])).

tff(c_86716,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86684,c_85998])).

tff(c_86721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_86716])).

tff(c_86723,plain,(
    m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_85960])).

tff(c_32,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_19,B_29),'#skF_3'(A_19,B_29)),A_19)
      | r7_relat_2(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_85753,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_85746,c_32])).

tff(c_85912,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_85753])).

tff(c_85913,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_85912])).

tff(c_85979,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_85913])).

tff(c_85997,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_85979])).

tff(c_86930,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86723,c_85997])).

tff(c_89769,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89760,c_86930])).

tff(c_89780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77314,c_89769])).

tff(c_89781,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_89759])).

tff(c_74945,plain,(
    ! [B_116607] :
      ( r3_orders_2('#skF_5',B_116607,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_116607,'#skF_7')
      | ~ m1_subset_1(B_116607,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_74944])).

tff(c_86891,plain,
    ( r3_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_86723,c_74945])).

tff(c_89419,plain,(
    ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_86891])).

tff(c_89783,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89781,c_89419])).

tff(c_89798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76031,c_89783])).

tff(c_89799,plain,(
    r3_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_86891])).

tff(c_93751,plain,(
    r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93750,c_89799])).

tff(c_93766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78030,c_93751])).

tff(c_93767,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_93749])).

tff(c_93796,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93767,c_32])).

tff(c_93987,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_85746,c_93796])).

tff(c_93988,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_93987])).

tff(c_93793,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93767,c_34])).

tff(c_93984,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_85746,c_93793])).

tff(c_93985,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_93984])).

tff(c_94326,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5'))
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),'#skF_8')
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_74584,c_93985])).

tff(c_94338,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_58994,c_58886,c_94326])).

tff(c_94355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93988,c_94338])).

tff(c_94356,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_85745])).

tff(c_94682,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94356,c_34])).

tff(c_94844,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_94682])).

tff(c_94845,plain,(
    ~ r2_hidden(k4_tarski('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_94844])).

tff(c_104964,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104950,c_94845])).

tff(c_94685,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94356,c_32])).

tff(c_94847,plain,
    ( ~ r2_hidden(k4_tarski('#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_94685])).

tff(c_94848,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_67432,c_94847])).

tff(c_104963,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_6'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104950,c_94848])).

tff(c_105179,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),'#skF_8')
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_74585,c_104963])).

tff(c_105191,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_58994,c_58895,c_105179])).

tff(c_105537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104964,c_105191])).

tff(c_105538,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_104949])).

tff(c_100907,plain,(
    ! [A_140252,A_140253,B_140254] :
      ( '#skF_3'(A_140252,k2_tarski(A_140253,B_140254)) = B_140254
      | '#skF_3'(A_140252,k2_tarski(A_140253,B_140254)) = A_140253
      | r7_relat_2(A_140252,k2_tarski(A_140253,B_140254))
      | ~ v1_relat_1(A_140252) ) ),
    inference(resolution,[status(thm)],[c_58956,c_12])).

tff(c_100910,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_100907,c_67432])).

tff(c_101284,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_100910])).

tff(c_101285,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_101284])).

tff(c_94971,plain,(
    ! [A_135117,A_135118,B_135119] :
      ( '#skF_3'(A_135117,k2_tarski(A_135118,B_135119)) = B_135119
      | '#skF_3'(A_135117,k2_tarski(A_135118,B_135119)) = A_135118
      | r7_relat_2(A_135117,k2_tarski(A_135118,B_135119))
      | ~ v1_relat_1(A_135117) ) ),
    inference(resolution,[status(thm)],[c_58956,c_12])).

tff(c_94974,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_94971,c_67432])).

tff(c_95287,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7'
    | '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74766,c_94974])).

tff(c_95288,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_95287])).

tff(c_94877,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_94845])).

tff(c_94898,plain,
    ( ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_94877])).

tff(c_94941,plain,(
    ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_94898])).

tff(c_95289,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95288,c_94941])).

tff(c_95294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_95289])).

tff(c_95295,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_95287])).

tff(c_95327,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95295,c_94941])).

tff(c_95332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_95327])).

tff(c_95334,plain,(
    m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_94898])).

tff(c_74949,plain,(
    ! [B_116607] :
      ( r3_orders_2('#skF_5',B_116607,'#skF_6')
      | ~ r1_orders_2('#skF_5',B_116607,'#skF_6')
      | ~ m1_subset_1(B_116607,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_74948])).

tff(c_95503,plain,
    ( r3_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_95334,c_74949])).

tff(c_98077,plain,(
    ~ r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_95503])).

tff(c_101286,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101285,c_98077])).

tff(c_101301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77314,c_101286])).

tff(c_101302,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_101284])).

tff(c_94921,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_94848])).

tff(c_94939,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_94921])).

tff(c_96749,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95334,c_94939])).

tff(c_101333,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101302,c_96749])).

tff(c_101347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76031,c_101333])).

tff(c_101349,plain,(
    r1_orders_2('#skF_5','#skF_3'(u1_orders_2('#skF_5'),k2_tarski('#skF_6','#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_95503])).

tff(c_105540,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105538,c_101349])).

tff(c_105555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58887,c_105540])).

tff(c_105556,plain,(
    v6_orders_2(k2_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_63223])).

tff(c_105564,plain,(
    ! [B_145433] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_145433,'#skF_6') = k2_tarski(B_145433,'#skF_6')
      | ~ m1_subset_1(B_145433,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63162,c_59016])).

tff(c_105567,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_105564])).

tff(c_105572,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6') = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_105567])).

tff(c_116797,plain,(
    ! [A_164510,C_164511,B_164512] :
      ( r3_orders_2(A_164510,C_164511,B_164512)
      | r3_orders_2(A_164510,B_164512,C_164511)
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(A_164510),B_164512,C_164511),k1_zfmisc_1(u1_struct_0(A_164510)))
      | ~ v6_orders_2(k7_domain_1(u1_struct_0(A_164510),B_164512,C_164511),A_164510)
      | ~ m1_subset_1(C_164511,u1_struct_0(A_164510))
      | ~ m1_subset_1(B_164512,u1_struct_0(A_164510))
      | ~ l1_orders_2(A_164510)
      | ~ v3_orders_2(A_164510)
      | v2_struct_0(A_164510) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_116821,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_7')
    | r3_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1(k2_tarski('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0('#skF_5'),'#skF_7','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_105572,c_116797])).

tff(c_116838,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_7')
    | r3_orders_2('#skF_5','#skF_7','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_72,c_105556,c_105572,c_63210,c_116821])).

tff(c_116839,plain,
    ( r3_orders_2('#skF_5','#skF_6','#skF_7')
    | r3_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_116838])).

tff(c_116847,plain,(
    r3_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_116839])).

tff(c_56,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_orders_2(A_52,B_53,C_54)
      | ~ r3_orders_2(A_52,B_53,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_116849,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_116847,c_56])).

tff(c_116852,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_72,c_116849])).

tff(c_116854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_58887,c_116852])).

tff(c_116855,plain,(
    r3_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_116839])).

tff(c_116858,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_116855,c_56])).

tff(c_116861,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_116858])).

tff(c_116863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63167,c_28323,c_116861])).

tff(c_116864,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_63166])).

tff(c_116869,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_116864])).

tff(c_116873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_116869])).

%------------------------------------------------------------------------------
