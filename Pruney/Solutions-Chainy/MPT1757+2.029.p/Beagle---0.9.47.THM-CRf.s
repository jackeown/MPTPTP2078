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
% DateTime   : Thu Dec  3 10:27:08 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 298 expanded)
%              Number of leaves         :   38 ( 128 expanded)
%              Depth                    :   20
%              Number of atoms          :  292 (1898 expanded)
%              Number of equality atoms :    5 (  95 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_231,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_188,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_32,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_80,plain,(
    ! [B_280,A_281] :
      ( l1_pre_topc(B_280)
      | ~ m1_pre_topc(B_280,A_281)
      | ~ l1_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86])).

tff(c_8,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_27] :
      ( m1_pre_topc(A_27,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_22,plain,(
    ! [B_26,A_24] :
      ( m1_subset_1(u1_struct_0(B_26),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_149,plain,(
    ! [B_299,A_300] :
      ( v3_pre_topc(u1_struct_0(B_299),A_300)
      | ~ v1_tsep_1(B_299,A_300)
      | ~ m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_156,plain,(
    ! [B_26,A_24] :
      ( v3_pre_topc(u1_struct_0(B_26),A_24)
      | ~ v1_tsep_1(B_26,A_24)
      | ~ v2_pre_topc(A_24)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_149])).

tff(c_101,plain,(
    ! [B_286,A_287] :
      ( m1_subset_1(u1_struct_0(B_286),k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ m1_pre_topc(B_286,A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_286,A_287] :
      ( r1_tarski(u1_struct_0(B_286),u1_struct_0(A_287))
      | ~ m1_pre_topc(B_286,A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_106,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_71,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_62])).

tff(c_109,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_71])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_192,plain,(
    ! [C_322,E_319,G_321,B_320,D_323,A_324] :
      ( r1_tmap_1(B_320,A_324,C_322,G_321)
      | ~ r1_tmap_1(D_323,A_324,k2_tmap_1(B_320,A_324,C_322,D_323),G_321)
      | ~ r1_tarski(E_319,u1_struct_0(D_323))
      | ~ r2_hidden(G_321,E_319)
      | ~ v3_pre_topc(E_319,B_320)
      | ~ m1_subset_1(G_321,u1_struct_0(D_323))
      | ~ m1_subset_1(G_321,u1_struct_0(B_320))
      | ~ m1_subset_1(E_319,k1_zfmisc_1(u1_struct_0(B_320)))
      | ~ m1_pre_topc(D_323,B_320)
      | v2_struct_0(D_323)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_320),u1_struct_0(A_324))))
      | ~ v1_funct_2(C_322,u1_struct_0(B_320),u1_struct_0(A_324))
      | ~ v1_funct_1(C_322)
      | ~ l1_pre_topc(B_320)
      | ~ v2_pre_topc(B_320)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_196,plain,(
    ! [E_319] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_319,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_319)
      | ~ v3_pre_topc(E_319,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_319,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_106,c_192])).

tff(c_203,plain,(
    ! [E_319] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_319,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_319)
      | ~ v3_pre_topc(E_319,'#skF_2')
      | ~ m1_subset_1(E_319,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_44,c_38,c_70,c_34,c_196])).

tff(c_205,plain,(
    ! [E_325] :
      ( ~ r1_tarski(E_325,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_325)
      | ~ v3_pre_topc(E_325,'#skF_2')
      | ~ m1_subset_1(E_325,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_42,c_109,c_203])).

tff(c_209,plain,(
    ! [B_26] :
      ( ~ r1_tarski(u1_struct_0(B_26),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_26))
      | ~ v3_pre_topc(u1_struct_0(B_26),'#skF_2')
      | ~ m1_pre_topc(B_26,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_205])).

tff(c_226,plain,(
    ! [B_327] :
      ( ~ r1_tarski(u1_struct_0(B_327),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_327))
      | ~ v3_pre_topc(u1_struct_0(B_327),'#skF_2')
      | ~ m1_pre_topc(B_327,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_209])).

tff(c_230,plain,(
    ! [B_286] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_286))
      | ~ v3_pre_topc(u1_struct_0(B_286),'#skF_2')
      | ~ m1_pre_topc(B_286,'#skF_2')
      | ~ m1_pre_topc(B_286,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105,c_226])).

tff(c_234,plain,(
    ! [B_328] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_328))
      | ~ v3_pre_topc(u1_struct_0(B_328),'#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_230])).

tff(c_238,plain,(
    ! [B_26] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_26))
      | ~ m1_pre_topc(B_26,'#skF_4')
      | ~ v1_tsep_1(B_26,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_26,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_156,c_234])).

tff(c_242,plain,(
    ! [B_329] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_329))
      | ~ m1_pre_topc(B_329,'#skF_4')
      | ~ v1_tsep_1(B_329,'#skF_2')
      | ~ m1_pre_topc(B_329,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_238])).

tff(c_247,plain,(
    ! [B_330] :
      ( ~ m1_pre_topc(B_330,'#skF_4')
      | ~ v1_tsep_1(B_330,'#skF_2')
      | ~ m1_pre_topc(B_330,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_330))
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_330)) ) ),
    inference(resolution,[status(thm)],[c_2,c_242])).

tff(c_256,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_264,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_256])).

tff(c_266,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_269,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_266])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_269])).

tff(c_274,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_296,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_274,c_12])).

tff(c_299,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_296])).

tff(c_303,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_299])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_303])).

tff(c_308,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_376,plain,(
    ! [B_350,D_354,A_351,F_353,C_352] :
      ( r1_tmap_1(D_354,A_351,k2_tmap_1(B_350,A_351,C_352,D_354),F_353)
      | ~ r1_tmap_1(B_350,A_351,C_352,F_353)
      | ~ m1_subset_1(F_353,u1_struct_0(D_354))
      | ~ m1_subset_1(F_353,u1_struct_0(B_350))
      | ~ m1_pre_topc(D_354,B_350)
      | v2_struct_0(D_354)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_350),u1_struct_0(A_351))))
      | ~ v1_funct_2(C_352,u1_struct_0(B_350),u1_struct_0(A_351))
      | ~ v1_funct_1(C_352)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_381,plain,(
    ! [D_354,F_353] :
      ( r1_tmap_1(D_354,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_354),F_353)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_353)
      | ~ m1_subset_1(F_353,u1_struct_0(D_354))
      | ~ m1_subset_1(F_353,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_354,'#skF_2')
      | v2_struct_0(D_354)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_376])).

tff(c_385,plain,(
    ! [D_354,F_353] :
      ( r1_tmap_1(D_354,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_354),F_353)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_353)
      | ~ m1_subset_1(F_353,u1_struct_0(D_354))
      | ~ m1_subset_1(F_353,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_354,'#skF_2')
      | v2_struct_0(D_354)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_381])).

tff(c_387,plain,(
    ! [D_355,F_356] :
      ( r1_tmap_1(D_355,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_355),F_356)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_356)
      | ~ m1_subset_1(F_356,u1_struct_0(D_355))
      | ~ m1_subset_1(F_356,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_355,'#skF_2')
      | v2_struct_0(D_355) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_385])).

tff(c_309,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_390,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_387,c_309])).

tff(c_393,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70,c_34,c_308,c_390])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.48  
% 3.01/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.48  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.01/1.48  
% 3.01/1.48  %Foreground sorts:
% 3.01/1.48  
% 3.01/1.48  
% 3.01/1.48  %Background operators:
% 3.01/1.48  
% 3.01/1.48  
% 3.01/1.48  %Foreground operators:
% 3.01/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.01/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.01/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.01/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.01/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.01/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.48  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.01/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.01/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.01/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.01/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.01/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.48  
% 3.24/1.50  tff(f_231, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.24/1.50  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.24/1.50  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.24/1.50  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.24/1.50  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.24/1.50  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.24/1.50  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.24/1.50  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.24/1.50  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.24/1.50  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.24/1.50  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.24/1.50  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_32, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.24/1.50  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_80, plain, (![B_280, A_281]: (l1_pre_topc(B_280) | ~m1_pre_topc(B_280, A_281) | ~l1_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.24/1.50  tff(c_86, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_80])).
% 3.24/1.50  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86])).
% 3.24/1.50  tff(c_8, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.50  tff(c_24, plain, (![A_27]: (m1_pre_topc(A_27, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.50  tff(c_40, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.50  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_22, plain, (![B_26, A_24]: (m1_subset_1(u1_struct_0(B_26), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.50  tff(c_149, plain, (![B_299, A_300]: (v3_pre_topc(u1_struct_0(B_299), A_300) | ~v1_tsep_1(B_299, A_300) | ~m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(u1_struct_0(A_300))) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.24/1.50  tff(c_156, plain, (![B_26, A_24]: (v3_pre_topc(u1_struct_0(B_26), A_24) | ~v1_tsep_1(B_26, A_24) | ~v2_pre_topc(A_24) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_22, c_149])).
% 3.24/1.50  tff(c_101, plain, (![B_286, A_287]: (m1_subset_1(u1_struct_0(B_286), k1_zfmisc_1(u1_struct_0(A_287))) | ~m1_pre_topc(B_286, A_287) | ~l1_pre_topc(A_287))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.24/1.50  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.50  tff(c_105, plain, (![B_286, A_287]: (r1_tarski(u1_struct_0(B_286), u1_struct_0(A_287)) | ~m1_pre_topc(B_286, A_287) | ~l1_pre_topc(A_287))), inference(resolution, [status(thm)], [c_101, c_4])).
% 3.24/1.50  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_68, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_69, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 3.24/1.50  tff(c_106, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_69])).
% 3.24/1.50  tff(c_62, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_71, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_62])).
% 3.24/1.50  tff(c_109, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_71])).
% 3.24/1.50  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.24/1.50  tff(c_192, plain, (![C_322, E_319, G_321, B_320, D_323, A_324]: (r1_tmap_1(B_320, A_324, C_322, G_321) | ~r1_tmap_1(D_323, A_324, k2_tmap_1(B_320, A_324, C_322, D_323), G_321) | ~r1_tarski(E_319, u1_struct_0(D_323)) | ~r2_hidden(G_321, E_319) | ~v3_pre_topc(E_319, B_320) | ~m1_subset_1(G_321, u1_struct_0(D_323)) | ~m1_subset_1(G_321, u1_struct_0(B_320)) | ~m1_subset_1(E_319, k1_zfmisc_1(u1_struct_0(B_320))) | ~m1_pre_topc(D_323, B_320) | v2_struct_0(D_323) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_320), u1_struct_0(A_324)))) | ~v1_funct_2(C_322, u1_struct_0(B_320), u1_struct_0(A_324)) | ~v1_funct_1(C_322) | ~l1_pre_topc(B_320) | ~v2_pre_topc(B_320) | v2_struct_0(B_320) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.24/1.50  tff(c_196, plain, (![E_319]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_319, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_319) | ~v3_pre_topc(E_319, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_319, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_106, c_192])).
% 3.24/1.50  tff(c_203, plain, (![E_319]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_319, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_319) | ~v3_pre_topc(E_319, '#skF_2') | ~m1_subset_1(E_319, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_44, c_38, c_70, c_34, c_196])).
% 3.24/1.50  tff(c_205, plain, (![E_325]: (~r1_tarski(E_325, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_325) | ~v3_pre_topc(E_325, '#skF_2') | ~m1_subset_1(E_325, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_42, c_109, c_203])).
% 3.24/1.50  tff(c_209, plain, (![B_26]: (~r1_tarski(u1_struct_0(B_26), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_26)) | ~v3_pre_topc(u1_struct_0(B_26), '#skF_2') | ~m1_pre_topc(B_26, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_205])).
% 3.24/1.50  tff(c_226, plain, (![B_327]: (~r1_tarski(u1_struct_0(B_327), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_327)) | ~v3_pre_topc(u1_struct_0(B_327), '#skF_2') | ~m1_pre_topc(B_327, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_209])).
% 3.24/1.50  tff(c_230, plain, (![B_286]: (~r2_hidden('#skF_6', u1_struct_0(B_286)) | ~v3_pre_topc(u1_struct_0(B_286), '#skF_2') | ~m1_pre_topc(B_286, '#skF_2') | ~m1_pre_topc(B_286, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_105, c_226])).
% 3.24/1.50  tff(c_234, plain, (![B_328]: (~r2_hidden('#skF_6', u1_struct_0(B_328)) | ~v3_pre_topc(u1_struct_0(B_328), '#skF_2') | ~m1_pre_topc(B_328, '#skF_2') | ~m1_pre_topc(B_328, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_230])).
% 3.24/1.50  tff(c_238, plain, (![B_26]: (~r2_hidden('#skF_6', u1_struct_0(B_26)) | ~m1_pre_topc(B_26, '#skF_4') | ~v1_tsep_1(B_26, '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(B_26, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_156, c_234])).
% 3.24/1.50  tff(c_242, plain, (![B_329]: (~r2_hidden('#skF_6', u1_struct_0(B_329)) | ~m1_pre_topc(B_329, '#skF_4') | ~v1_tsep_1(B_329, '#skF_2') | ~m1_pre_topc(B_329, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_238])).
% 3.24/1.50  tff(c_247, plain, (![B_330]: (~m1_pre_topc(B_330, '#skF_4') | ~v1_tsep_1(B_330, '#skF_2') | ~m1_pre_topc(B_330, '#skF_2') | v1_xboole_0(u1_struct_0(B_330)) | ~m1_subset_1('#skF_6', u1_struct_0(B_330)))), inference(resolution, [status(thm)], [c_2, c_242])).
% 3.24/1.50  tff(c_256, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_247])).
% 3.24/1.50  tff(c_264, plain, (~m1_pre_topc('#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_256])).
% 3.24/1.50  tff(c_266, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_264])).
% 3.24/1.50  tff(c_269, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_266])).
% 3.24/1.50  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_269])).
% 3.24/1.50  tff(c_274, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_264])).
% 3.24/1.50  tff(c_12, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.24/1.50  tff(c_296, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_274, c_12])).
% 3.24/1.50  tff(c_299, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_296])).
% 3.24/1.50  tff(c_303, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_299])).
% 3.24/1.50  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_303])).
% 3.24/1.50  tff(c_308, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.24/1.50  tff(c_376, plain, (![B_350, D_354, A_351, F_353, C_352]: (r1_tmap_1(D_354, A_351, k2_tmap_1(B_350, A_351, C_352, D_354), F_353) | ~r1_tmap_1(B_350, A_351, C_352, F_353) | ~m1_subset_1(F_353, u1_struct_0(D_354)) | ~m1_subset_1(F_353, u1_struct_0(B_350)) | ~m1_pre_topc(D_354, B_350) | v2_struct_0(D_354) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_350), u1_struct_0(A_351)))) | ~v1_funct_2(C_352, u1_struct_0(B_350), u1_struct_0(A_351)) | ~v1_funct_1(C_352) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.24/1.50  tff(c_381, plain, (![D_354, F_353]: (r1_tmap_1(D_354, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_354), F_353) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_353) | ~m1_subset_1(F_353, u1_struct_0(D_354)) | ~m1_subset_1(F_353, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_354, '#skF_2') | v2_struct_0(D_354) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_376])).
% 3.24/1.50  tff(c_385, plain, (![D_354, F_353]: (r1_tmap_1(D_354, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_354), F_353) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_353) | ~m1_subset_1(F_353, u1_struct_0(D_354)) | ~m1_subset_1(F_353, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_354, '#skF_2') | v2_struct_0(D_354) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_381])).
% 3.24/1.50  tff(c_387, plain, (![D_355, F_356]: (r1_tmap_1(D_355, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_355), F_356) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_356) | ~m1_subset_1(F_356, u1_struct_0(D_355)) | ~m1_subset_1(F_356, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_355, '#skF_2') | v2_struct_0(D_355))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_385])).
% 3.24/1.50  tff(c_309, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.24/1.50  tff(c_390, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_387, c_309])).
% 3.24/1.50  tff(c_393, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_70, c_34, c_308, c_390])).
% 3.24/1.50  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_393])).
% 3.24/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.50  
% 3.24/1.50  Inference rules
% 3.24/1.50  ----------------------
% 3.24/1.50  #Ref     : 0
% 3.24/1.50  #Sup     : 57
% 3.24/1.50  #Fact    : 0
% 3.24/1.50  #Define  : 0
% 3.24/1.50  #Split   : 3
% 3.24/1.50  #Chain   : 0
% 3.24/1.50  #Close   : 0
% 3.24/1.50  
% 3.24/1.50  Ordering : KBO
% 3.24/1.50  
% 3.24/1.50  Simplification rules
% 3.24/1.50  ----------------------
% 3.24/1.50  #Subsume      : 16
% 3.24/1.50  #Demod        : 73
% 3.24/1.50  #Tautology    : 17
% 3.24/1.50  #SimpNegUnit  : 17
% 3.24/1.50  #BackRed      : 0
% 3.24/1.50  
% 3.24/1.50  #Partial instantiations: 0
% 3.24/1.50  #Strategies tried      : 1
% 3.24/1.50  
% 3.24/1.50  Timing (in seconds)
% 3.24/1.50  ----------------------
% 3.24/1.51  Preprocessing        : 0.37
% 3.24/1.51  Parsing              : 0.18
% 3.24/1.51  CNF conversion       : 0.05
% 3.24/1.51  Main loop            : 0.29
% 3.24/1.51  Inferencing          : 0.10
% 3.24/1.51  Reduction            : 0.09
% 3.24/1.51  Demodulation         : 0.06
% 3.24/1.51  BG Simplification    : 0.02
% 3.24/1.51  Subsumption          : 0.06
% 3.24/1.51  Abstraction          : 0.01
% 3.24/1.51  MUC search           : 0.00
% 3.24/1.51  Cooper               : 0.00
% 3.24/1.51  Total                : 0.70
% 3.24/1.51  Index Insertion      : 0.00
% 3.24/1.51  Index Deletion       : 0.00
% 3.24/1.51  Index Matching       : 0.00
% 3.24/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
