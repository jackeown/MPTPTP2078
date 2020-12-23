%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1774+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:21 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 211 expanded)
%              Number of leaves         :   33 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 (1822 expanded)
%              Number of equality atoms :    5 (  74 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_20,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_22,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_201,plain,(
    ! [B_681,C_682,A_683] :
      ( r1_tarski(u1_struct_0(B_681),u1_struct_0(C_682))
      | ~ m1_pre_topc(B_681,C_682)
      | ~ m1_pre_topc(C_682,A_683)
      | ~ m1_pre_topc(B_681,A_683)
      | ~ l1_pre_topc(A_683)
      | ~ v2_pre_topc(A_683) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_205,plain,(
    ! [B_681] :
      ( r1_tarski(u1_struct_0(B_681),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_681,'#skF_4')
      | ~ m1_pre_topc(B_681,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_201])).

tff(c_231,plain,(
    ! [B_685] :
      ( r1_tarski(u1_struct_0(B_685),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_685,'#skF_4')
      | ~ m1_pre_topc(B_685,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_205])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_284,plain,(
    ! [A_691,B_692] :
      ( r1_tarski(A_691,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_691,u1_struct_0(B_692))
      | ~ m1_pre_topc(B_692,'#skF_4')
      | ~ m1_pre_topc(B_692,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_231,c_2])).

tff(c_296,plain,
    ( r1_tarski('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_284])).

tff(c_310,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_296])).

tff(c_24,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_8,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_113,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_157,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_69])).

tff(c_484,plain,(
    ! [A_711,B_712,D_708,F_713,E_710,H_714,C_709] :
      ( r1_tmap_1(D_708,B_712,E_710,H_714)
      | ~ r1_tmap_1(C_709,B_712,k3_tmap_1(A_711,B_712,D_708,C_709,E_710),H_714)
      | ~ r1_tarski(F_713,u1_struct_0(C_709))
      | ~ r2_hidden(H_714,F_713)
      | ~ v3_pre_topc(F_713,D_708)
      | ~ m1_subset_1(H_714,u1_struct_0(C_709))
      | ~ m1_subset_1(H_714,u1_struct_0(D_708))
      | ~ m1_subset_1(F_713,k1_zfmisc_1(u1_struct_0(D_708)))
      | ~ m1_pre_topc(C_709,D_708)
      | ~ m1_subset_1(E_710,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_708),u1_struct_0(B_712))))
      | ~ v1_funct_2(E_710,u1_struct_0(D_708),u1_struct_0(B_712))
      | ~ v1_funct_1(E_710)
      | ~ m1_pre_topc(D_708,A_711)
      | v2_struct_0(D_708)
      | ~ m1_pre_topc(C_709,A_711)
      | v2_struct_0(C_709)
      | ~ l1_pre_topc(B_712)
      | ~ v2_pre_topc(B_712)
      | v2_struct_0(B_712)
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_488,plain,(
    ! [F_713] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_713,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_713)
      | ~ v3_pre_topc(F_713,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_713,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_157,c_484])).

tff(c_495,plain,(
    ! [F_713] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_713,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_713)
      | ~ v3_pre_topc(F_713,'#skF_4')
      | ~ m1_subset_1(F_713,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58,c_56,c_46,c_42,c_40,c_38,c_36,c_34,c_71,c_28,c_488])).

tff(c_497,plain,(
    ! [F_715] :
      ( ~ r1_tarski(F_715,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_715)
      | ~ v3_pre_topc(F_715,'#skF_4')
      | ~ m1_subset_1(F_715,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_48,c_44,c_113,c_495])).

tff(c_503,plain,(
    ! [A_716] :
      ( ~ r1_tarski(A_716,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',A_716)
      | ~ v3_pre_topc(A_716,'#skF_4')
      | ~ r1_tarski(A_716,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_497])).

tff(c_512,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_503])).

tff(c_517,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_72,c_512])).

tff(c_26,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_247,plain,(
    ! [D_686,C_687,A_688] :
      ( v3_pre_topc(D_686,C_687)
      | ~ m1_subset_1(D_686,k1_zfmisc_1(u1_struct_0(C_687)))
      | ~ v3_pre_topc(D_686,A_688)
      | ~ m1_pre_topc(C_687,A_688)
      | ~ m1_subset_1(D_686,k1_zfmisc_1(u1_struct_0(A_688)))
      | ~ l1_pre_topc(A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_539,plain,(
    ! [A_719,C_720,A_721] :
      ( v3_pre_topc(A_719,C_720)
      | ~ v3_pre_topc(A_719,A_721)
      | ~ m1_pre_topc(C_720,A_721)
      | ~ m1_subset_1(A_719,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ l1_pre_topc(A_721)
      | ~ r1_tarski(A_719,u1_struct_0(C_720)) ) ),
    inference(resolution,[status(thm)],[c_8,c_247])).

tff(c_543,plain,(
    ! [A_719] :
      ( v3_pre_topc(A_719,'#skF_4')
      | ~ v3_pre_topc(A_719,'#skF_2')
      | ~ m1_subset_1(A_719,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_719,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_539])).

tff(c_598,plain,(
    ! [A_726] :
      ( v3_pre_topc(A_726,'#skF_4')
      | ~ v3_pre_topc(A_726,'#skF_2')
      | ~ m1_subset_1(A_726,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_726,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_543])).

tff(c_605,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_598])).

tff(c_609,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_26,c_605])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_609])).

tff(c_613,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_928,plain,(
    ! [G_755,E_760,C_759,B_757,A_756,D_758] :
      ( r1_tmap_1(D_758,B_757,k3_tmap_1(A_756,B_757,C_759,D_758,E_760),G_755)
      | ~ r1_tmap_1(C_759,B_757,E_760,G_755)
      | ~ m1_pre_topc(D_758,C_759)
      | ~ m1_subset_1(G_755,u1_struct_0(D_758))
      | ~ m1_subset_1(G_755,u1_struct_0(C_759))
      | ~ m1_subset_1(E_760,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_759),u1_struct_0(B_757))))
      | ~ v1_funct_2(E_760,u1_struct_0(C_759),u1_struct_0(B_757))
      | ~ v1_funct_1(E_760)
      | ~ m1_pre_topc(D_758,A_756)
      | v2_struct_0(D_758)
      | ~ m1_pre_topc(C_759,A_756)
      | v2_struct_0(C_759)
      | ~ l1_pre_topc(B_757)
      | ~ v2_pre_topc(B_757)
      | v2_struct_0(B_757)
      | ~ l1_pre_topc(A_756)
      | ~ v2_pre_topc(A_756)
      | v2_struct_0(A_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_930,plain,(
    ! [D_758,A_756,G_755] :
      ( r1_tmap_1(D_758,'#skF_1',k3_tmap_1(A_756,'#skF_1','#skF_4',D_758,'#skF_5'),G_755)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_755)
      | ~ m1_pre_topc(D_758,'#skF_4')
      | ~ m1_subset_1(G_755,u1_struct_0(D_758))
      | ~ m1_subset_1(G_755,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_758,A_756)
      | v2_struct_0(D_758)
      | ~ m1_pre_topc('#skF_4',A_756)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_756)
      | ~ v2_pre_topc(A_756)
      | v2_struct_0(A_756) ) ),
    inference(resolution,[status(thm)],[c_36,c_928])).

tff(c_936,plain,(
    ! [D_758,A_756,G_755] :
      ( r1_tmap_1(D_758,'#skF_1',k3_tmap_1(A_756,'#skF_1','#skF_4',D_758,'#skF_5'),G_755)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_755)
      | ~ m1_pre_topc(D_758,'#skF_4')
      | ~ m1_subset_1(G_755,u1_struct_0(D_758))
      | ~ m1_subset_1(G_755,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_758,A_756)
      | v2_struct_0(D_758)
      | ~ m1_pre_topc('#skF_4',A_756)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_756)
      | ~ v2_pre_topc(A_756)
      | v2_struct_0(A_756) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_38,c_930])).

tff(c_983,plain,(
    ! [D_763,A_764,G_765] :
      ( r1_tmap_1(D_763,'#skF_1',k3_tmap_1(A_764,'#skF_1','#skF_4',D_763,'#skF_5'),G_765)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_765)
      | ~ m1_pre_topc(D_763,'#skF_4')
      | ~ m1_subset_1(G_765,u1_struct_0(D_763))
      | ~ m1_subset_1(G_765,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_763,A_764)
      | v2_struct_0(D_763)
      | ~ m1_pre_topc('#skF_4',A_764)
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_936])).

tff(c_612,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_986,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_983,c_612])).

tff(c_989,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_42,c_46,c_71,c_28,c_34,c_613,c_986])).

tff(c_991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_989])).

%------------------------------------------------------------------------------
