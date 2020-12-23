%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 226 expanded)
%              Number of leaves         :   33 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  305 (1752 expanded)
%              Number of equality atoms :    4 (  83 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

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
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_28,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_26,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_30,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_139,plain,(
    ! [B_294,A_295,C_296,D_297] :
      ( r2_hidden(B_294,k1_tops_1(A_295,C_296))
      | ~ r2_hidden(B_294,D_297)
      | ~ r1_tarski(D_297,C_296)
      | ~ v3_pre_topc(D_297,A_295)
      | ~ m1_subset_1(D_297,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ m1_subset_1(C_296,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [A_299,C_300] :
      ( r2_hidden('#skF_8',k1_tops_1(A_299,C_300))
      | ~ r1_tarski('#skF_6',C_300)
      | ~ v3_pre_topc('#skF_6',A_299)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(resolution,[status(thm)],[c_72,c_139])).

tff(c_152,plain,(
    ! [C_300] :
      ( r2_hidden('#skF_8',k1_tops_1('#skF_3',C_300))
      | ~ r1_tarski('#skF_6',C_300)
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_156,plain,(
    ! [C_301] :
      ( r2_hidden('#skF_8',k1_tops_1('#skF_3',C_301))
      | ~ r1_tarski('#skF_6',C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_32,c_152])).

tff(c_163,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_3','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_169,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_163])).

tff(c_18,plain,(
    ! [C_21,A_15,B_19] :
      ( m1_connsp_2(C_21,A_15,B_19)
      | ~ r2_hidden(B_19,k1_tops_1(A_15,C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_173,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_18])).

tff(c_181,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_70,c_38,c_173])).

tff(c_182,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_181])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_7')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_90,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_71,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_92,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_71])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_269,plain,(
    ! [G_333,C_331,D_328,A_330,B_329,E_332] :
      ( r1_tmap_1(B_329,A_330,C_331,G_333)
      | ~ r1_tmap_1(D_328,A_330,k2_tmap_1(B_329,A_330,C_331,D_328),G_333)
      | ~ m1_connsp_2(E_332,B_329,G_333)
      | ~ r1_tarski(E_332,u1_struct_0(D_328))
      | ~ m1_subset_1(G_333,u1_struct_0(D_328))
      | ~ m1_subset_1(G_333,u1_struct_0(B_329))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(u1_struct_0(B_329)))
      | ~ m1_pre_topc(D_328,B_329)
      | v2_struct_0(D_328)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_329),u1_struct_0(A_330))))
      | ~ v1_funct_2(C_331,u1_struct_0(B_329),u1_struct_0(A_330))
      | ~ v1_funct_1(C_331)
      | ~ l1_pre_topc(B_329)
      | ~ v2_pre_topc(B_329)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_271,plain,(
    ! [E_332] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_332,'#skF_3','#skF_8')
      | ~ r1_tarski(E_332,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_90,c_269])).

tff(c_274,plain,(
    ! [E_332] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_332,'#skF_3','#skF_8')
      | ~ r1_tarski(E_332,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_44,c_40,c_70,c_34,c_271])).

tff(c_276,plain,(
    ! [E_334] :
      ( ~ m1_connsp_2(E_334,'#skF_3','#skF_8')
      | ~ r1_tarski(E_334,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_334,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_42,c_92,c_274])).

tff(c_283,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_276])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_182,c_283])).

tff(c_291,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_342,plain,(
    ! [B_358,A_359,C_360,D_361] :
      ( r2_hidden(B_358,k1_tops_1(A_359,C_360))
      | ~ r2_hidden(B_358,D_361)
      | ~ r1_tarski(D_361,C_360)
      | ~ v3_pre_topc(D_361,A_359)
      | ~ m1_subset_1(D_361,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_352,plain,(
    ! [A_362,C_363] :
      ( r2_hidden('#skF_8',k1_tops_1(A_362,C_363))
      | ~ r1_tarski('#skF_6',C_363)
      | ~ v3_pre_topc('#skF_6',A_362)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362) ) ),
    inference(resolution,[status(thm)],[c_72,c_342])).

tff(c_354,plain,(
    ! [C_363] :
      ( r2_hidden('#skF_8',k1_tops_1('#skF_3',C_363))
      | ~ r1_tarski('#skF_6',C_363)
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(C_363,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_352])).

tff(c_358,plain,(
    ! [C_364] :
      ( r2_hidden('#skF_8',k1_tops_1('#skF_3',C_364))
      | ~ r1_tarski('#skF_6',C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_32,c_354])).

tff(c_365,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_3','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_358])).

tff(c_371,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_365])).

tff(c_375,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_371,c_18])).

tff(c_383,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_70,c_38,c_375])).

tff(c_384,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_383])).

tff(c_429,plain,(
    ! [B_383,E_386,A_384,G_387,D_382,C_385] :
      ( r1_tmap_1(D_382,A_384,k2_tmap_1(B_383,A_384,C_385,D_382),G_387)
      | ~ r1_tmap_1(B_383,A_384,C_385,G_387)
      | ~ m1_connsp_2(E_386,B_383,G_387)
      | ~ r1_tarski(E_386,u1_struct_0(D_382))
      | ~ m1_subset_1(G_387,u1_struct_0(D_382))
      | ~ m1_subset_1(G_387,u1_struct_0(B_383))
      | ~ m1_subset_1(E_386,k1_zfmisc_1(u1_struct_0(B_383)))
      | ~ m1_pre_topc(D_382,B_383)
      | v2_struct_0(D_382)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_383),u1_struct_0(A_384))))
      | ~ v1_funct_2(C_385,u1_struct_0(B_383),u1_struct_0(A_384))
      | ~ v1_funct_1(C_385)
      | ~ l1_pre_topc(B_383)
      | ~ v2_pre_topc(B_383)
      | v2_struct_0(B_383)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_431,plain,(
    ! [D_382,A_384,C_385] :
      ( r1_tmap_1(D_382,A_384,k2_tmap_1('#skF_3',A_384,C_385,D_382),'#skF_8')
      | ~ r1_tmap_1('#skF_3',A_384,C_385,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_382))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_382))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(D_382,'#skF_3')
      | v2_struct_0(D_382)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_384))))
      | ~ v1_funct_2(C_385,u1_struct_0('#skF_3'),u1_struct_0(A_384))
      | ~ v1_funct_1(C_385)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(resolution,[status(thm)],[c_384,c_429])).

tff(c_434,plain,(
    ! [D_382,A_384,C_385] :
      ( r1_tmap_1(D_382,A_384,k2_tmap_1('#skF_3',A_384,C_385,D_382),'#skF_8')
      | ~ r1_tmap_1('#skF_3',A_384,C_385,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_382))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_382))
      | ~ m1_pre_topc(D_382,'#skF_3')
      | v2_struct_0(D_382)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_384))))
      | ~ v1_funct_2(C_385,u1_struct_0('#skF_3'),u1_struct_0(A_384))
      | ~ v1_funct_1(C_385)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_38,c_70,c_431])).

tff(c_454,plain,(
    ! [D_393,A_394,C_395] :
      ( r1_tmap_1(D_393,A_394,k2_tmap_1('#skF_3',A_394,C_395,D_393),'#skF_8')
      | ~ r1_tmap_1('#skF_3',A_394,C_395,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_393))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_393))
      | ~ m1_pre_topc(D_393,'#skF_3')
      | v2_struct_0(D_393)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_394))))
      | ~ v1_funct_2(C_395,u1_struct_0('#skF_3'),u1_struct_0(A_394))
      | ~ v1_funct_1(C_395)
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_434])).

tff(c_456,plain,(
    ! [D_393] :
      ( r1_tmap_1(D_393,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_393),'#skF_8')
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_393))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_393))
      | ~ m1_pre_topc(D_393,'#skF_3')
      | v2_struct_0(D_393)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_454])).

tff(c_459,plain,(
    ! [D_393] :
      ( r1_tmap_1(D_393,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_393),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_393))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_393))
      | ~ m1_pre_topc(D_393,'#skF_3')
      | v2_struct_0(D_393)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_48,c_46,c_291,c_456])).

tff(c_461,plain,(
    ! [D_396] :
      ( r1_tmap_1(D_396,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_396),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_396))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_396))
      | ~ m1_pre_topc(D_396,'#skF_3')
      | v2_struct_0(D_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_459])).

tff(c_292,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_466,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_461,c_292])).

tff(c_473,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_28,c_466])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:52:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.57  
% 3.63/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.57  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.63/1.57  
% 3.63/1.57  %Foreground sorts:
% 3.63/1.57  
% 3.63/1.57  
% 3.63/1.57  %Background operators:
% 3.63/1.57  
% 3.63/1.57  
% 3.63/1.57  %Foreground operators:
% 3.63/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.63/1.57  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.63/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.63/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.63/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.63/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.63/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.63/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.63/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.63/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.63/1.57  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.63/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.63/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.63/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.63/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.63/1.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.63/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.57  
% 3.63/1.61  tff(f_163, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.63/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.63/1.61  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 3.63/1.61  tff(f_66, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.63/1.61  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.63/1.61  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_34, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_28, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_46, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_26, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_70, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 3.63/1.61  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.63/1.61  tff(c_32, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_30, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.63/1.61  tff(c_139, plain, (![B_294, A_295, C_296, D_297]: (r2_hidden(B_294, k1_tops_1(A_295, C_296)) | ~r2_hidden(B_294, D_297) | ~r1_tarski(D_297, C_296) | ~v3_pre_topc(D_297, A_295) | ~m1_subset_1(D_297, k1_zfmisc_1(u1_struct_0(A_295))) | ~m1_subset_1(C_296, k1_zfmisc_1(u1_struct_0(A_295))) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.61  tff(c_150, plain, (![A_299, C_300]: (r2_hidden('#skF_8', k1_tops_1(A_299, C_300)) | ~r1_tarski('#skF_6', C_300) | ~v3_pre_topc('#skF_6', A_299) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_299))) | ~m1_subset_1(C_300, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(resolution, [status(thm)], [c_72, c_139])).
% 3.63/1.61  tff(c_152, plain, (![C_300]: (r2_hidden('#skF_8', k1_tops_1('#skF_3', C_300)) | ~r1_tarski('#skF_6', C_300) | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(C_300, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_150])).
% 3.63/1.61  tff(c_156, plain, (![C_301]: (r2_hidden('#skF_8', k1_tops_1('#skF_3', C_301)) | ~r1_tarski('#skF_6', C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_32, c_152])).
% 3.63/1.61  tff(c_163, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_3', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_156])).
% 3.63/1.61  tff(c_169, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_163])).
% 3.63/1.61  tff(c_18, plain, (![C_21, A_15, B_19]: (m1_connsp_2(C_21, A_15, B_19) | ~r2_hidden(B_19, k1_tops_1(A_15, C_21)) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, u1_struct_0(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.63/1.61  tff(c_173, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_169, c_18])).
% 3.63/1.61  tff(c_181, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_70, c_38, c_173])).
% 3.63/1.61  tff(c_182, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_181])).
% 3.63/1.61  tff(c_68, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_7') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_69, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 3.63/1.61  tff(c_90, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_69])).
% 3.63/1.61  tff(c_62, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_71, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 3.63/1.61  tff(c_92, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_71])).
% 3.63/1.61  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.63/1.61  tff(c_269, plain, (![G_333, C_331, D_328, A_330, B_329, E_332]: (r1_tmap_1(B_329, A_330, C_331, G_333) | ~r1_tmap_1(D_328, A_330, k2_tmap_1(B_329, A_330, C_331, D_328), G_333) | ~m1_connsp_2(E_332, B_329, G_333) | ~r1_tarski(E_332, u1_struct_0(D_328)) | ~m1_subset_1(G_333, u1_struct_0(D_328)) | ~m1_subset_1(G_333, u1_struct_0(B_329)) | ~m1_subset_1(E_332, k1_zfmisc_1(u1_struct_0(B_329))) | ~m1_pre_topc(D_328, B_329) | v2_struct_0(D_328) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_329), u1_struct_0(A_330)))) | ~v1_funct_2(C_331, u1_struct_0(B_329), u1_struct_0(A_330)) | ~v1_funct_1(C_331) | ~l1_pre_topc(B_329) | ~v2_pre_topc(B_329) | v2_struct_0(B_329) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330) | v2_struct_0(A_330))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.63/1.61  tff(c_271, plain, (![E_332]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_connsp_2(E_332, '#skF_3', '#skF_8') | ~r1_tarski(E_332, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1(E_332, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_90, c_269])).
% 3.63/1.61  tff(c_274, plain, (![E_332]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_connsp_2(E_332, '#skF_3', '#skF_8') | ~r1_tarski(E_332, u1_struct_0('#skF_5')) | ~m1_subset_1(E_332, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_44, c_40, c_70, c_34, c_271])).
% 3.63/1.61  tff(c_276, plain, (![E_334]: (~m1_connsp_2(E_334, '#skF_3', '#skF_8') | ~r1_tarski(E_334, u1_struct_0('#skF_5')) | ~m1_subset_1(E_334, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_42, c_92, c_274])).
% 3.63/1.61  tff(c_283, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_276])).
% 3.63/1.61  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_182, c_283])).
% 3.63/1.61  tff(c_291, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_69])).
% 3.63/1.61  tff(c_342, plain, (![B_358, A_359, C_360, D_361]: (r2_hidden(B_358, k1_tops_1(A_359, C_360)) | ~r2_hidden(B_358, D_361) | ~r1_tarski(D_361, C_360) | ~v3_pre_topc(D_361, A_359) | ~m1_subset_1(D_361, k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(A_359))) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.61  tff(c_352, plain, (![A_362, C_363]: (r2_hidden('#skF_8', k1_tops_1(A_362, C_363)) | ~r1_tarski('#skF_6', C_363) | ~v3_pre_topc('#skF_6', A_362) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_subset_1(C_363, k1_zfmisc_1(u1_struct_0(A_362))) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362))), inference(resolution, [status(thm)], [c_72, c_342])).
% 3.63/1.61  tff(c_354, plain, (![C_363]: (r2_hidden('#skF_8', k1_tops_1('#skF_3', C_363)) | ~r1_tarski('#skF_6', C_363) | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(C_363, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_352])).
% 3.63/1.61  tff(c_358, plain, (![C_364]: (r2_hidden('#skF_8', k1_tops_1('#skF_3', C_364)) | ~r1_tarski('#skF_6', C_364) | ~m1_subset_1(C_364, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_32, c_354])).
% 3.63/1.61  tff(c_365, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_3', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_358])).
% 3.63/1.61  tff(c_371, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_365])).
% 3.63/1.61  tff(c_375, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_371, c_18])).
% 3.63/1.61  tff(c_383, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_70, c_38, c_375])).
% 3.63/1.61  tff(c_384, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_383])).
% 3.63/1.61  tff(c_429, plain, (![B_383, E_386, A_384, G_387, D_382, C_385]: (r1_tmap_1(D_382, A_384, k2_tmap_1(B_383, A_384, C_385, D_382), G_387) | ~r1_tmap_1(B_383, A_384, C_385, G_387) | ~m1_connsp_2(E_386, B_383, G_387) | ~r1_tarski(E_386, u1_struct_0(D_382)) | ~m1_subset_1(G_387, u1_struct_0(D_382)) | ~m1_subset_1(G_387, u1_struct_0(B_383)) | ~m1_subset_1(E_386, k1_zfmisc_1(u1_struct_0(B_383))) | ~m1_pre_topc(D_382, B_383) | v2_struct_0(D_382) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_383), u1_struct_0(A_384)))) | ~v1_funct_2(C_385, u1_struct_0(B_383), u1_struct_0(A_384)) | ~v1_funct_1(C_385) | ~l1_pre_topc(B_383) | ~v2_pre_topc(B_383) | v2_struct_0(B_383) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384) | v2_struct_0(A_384))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.63/1.61  tff(c_431, plain, (![D_382, A_384, C_385]: (r1_tmap_1(D_382, A_384, k2_tmap_1('#skF_3', A_384, C_385, D_382), '#skF_8') | ~r1_tmap_1('#skF_3', A_384, C_385, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_382)) | ~m1_subset_1('#skF_8', u1_struct_0(D_382)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(D_382, '#skF_3') | v2_struct_0(D_382) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_384)))) | ~v1_funct_2(C_385, u1_struct_0('#skF_3'), u1_struct_0(A_384)) | ~v1_funct_1(C_385) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384) | v2_struct_0(A_384))), inference(resolution, [status(thm)], [c_384, c_429])).
% 3.63/1.61  tff(c_434, plain, (![D_382, A_384, C_385]: (r1_tmap_1(D_382, A_384, k2_tmap_1('#skF_3', A_384, C_385, D_382), '#skF_8') | ~r1_tmap_1('#skF_3', A_384, C_385, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_382)) | ~m1_subset_1('#skF_8', u1_struct_0(D_382)) | ~m1_pre_topc(D_382, '#skF_3') | v2_struct_0(D_382) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_384)))) | ~v1_funct_2(C_385, u1_struct_0('#skF_3'), u1_struct_0(A_384)) | ~v1_funct_1(C_385) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384) | v2_struct_0(A_384))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_38, c_70, c_431])).
% 3.63/1.61  tff(c_454, plain, (![D_393, A_394, C_395]: (r1_tmap_1(D_393, A_394, k2_tmap_1('#skF_3', A_394, C_395, D_393), '#skF_8') | ~r1_tmap_1('#skF_3', A_394, C_395, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_393)) | ~m1_subset_1('#skF_8', u1_struct_0(D_393)) | ~m1_pre_topc(D_393, '#skF_3') | v2_struct_0(D_393) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_394)))) | ~v1_funct_2(C_395, u1_struct_0('#skF_3'), u1_struct_0(A_394)) | ~v1_funct_1(C_395) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394))), inference(negUnitSimplification, [status(thm)], [c_54, c_434])).
% 3.63/1.61  tff(c_456, plain, (![D_393]: (r1_tmap_1(D_393, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_393), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_393)) | ~m1_subset_1('#skF_8', u1_struct_0(D_393)) | ~m1_pre_topc(D_393, '#skF_3') | v2_struct_0(D_393) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_454])).
% 3.63/1.61  tff(c_459, plain, (![D_393]: (r1_tmap_1(D_393, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_393), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_393)) | ~m1_subset_1('#skF_8', u1_struct_0(D_393)) | ~m1_pre_topc(D_393, '#skF_3') | v2_struct_0(D_393) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_48, c_46, c_291, c_456])).
% 3.63/1.61  tff(c_461, plain, (![D_396]: (r1_tmap_1(D_396, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_396), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_396)) | ~m1_subset_1('#skF_8', u1_struct_0(D_396)) | ~m1_pre_topc(D_396, '#skF_3') | v2_struct_0(D_396))), inference(negUnitSimplification, [status(thm)], [c_60, c_459])).
% 3.63/1.61  tff(c_292, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_69])).
% 3.63/1.61  tff(c_466, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_461, c_292])).
% 3.63/1.61  tff(c_473, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_28, c_466])).
% 3.63/1.61  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_473])).
% 3.63/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.61  
% 3.63/1.61  Inference rules
% 3.63/1.61  ----------------------
% 3.63/1.61  #Ref     : 0
% 3.63/1.61  #Sup     : 71
% 3.63/1.61  #Fact    : 0
% 3.63/1.61  #Define  : 0
% 3.63/1.61  #Split   : 4
% 3.63/1.61  #Chain   : 0
% 3.63/1.61  #Close   : 0
% 3.63/1.61  
% 3.63/1.61  Ordering : KBO
% 3.63/1.61  
% 3.63/1.61  Simplification rules
% 3.63/1.61  ----------------------
% 3.63/1.61  #Subsume      : 5
% 3.63/1.61  #Demod        : 139
% 3.63/1.61  #Tautology    : 9
% 3.63/1.61  #SimpNegUnit  : 17
% 3.63/1.61  #BackRed      : 0
% 3.63/1.61  
% 3.63/1.61  #Partial instantiations: 0
% 3.63/1.61  #Strategies tried      : 1
% 3.63/1.61  
% 3.63/1.61  Timing (in seconds)
% 3.63/1.61  ----------------------
% 3.63/1.61  Preprocessing        : 0.37
% 3.63/1.61  Parsing              : 0.19
% 3.63/1.61  CNF conversion       : 0.05
% 3.63/1.61  Main loop            : 0.46
% 3.63/1.61  Inferencing          : 0.17
% 3.63/1.61  Reduction            : 0.15
% 3.63/1.61  Demodulation         : 0.11
% 3.63/1.61  BG Simplification    : 0.02
% 3.63/1.61  Subsumption          : 0.09
% 3.63/1.61  Abstraction          : 0.02
% 3.63/1.61  MUC search           : 0.00
% 3.63/1.61  Cooper               : 0.00
% 3.63/1.61  Total                : 0.90
% 3.63/1.61  Index Insertion      : 0.00
% 3.63/1.61  Index Deletion       : 0.00
% 3.63/1.61  Index Matching       : 0.00
% 3.63/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
